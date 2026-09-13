"""Exact usage ingestion and explicit, auditable estimates from comparable windows."""
from __future__ import annotations

import datetime as dt
import json
import math
from pathlib import Path
import statistics
import time
import uuid
import re

from es.errors import UsageError
from es.store import Store

FIELDS = ('input_tokens', 'cached_input_tokens', 'output_tokens', 'reasoning_output_tokens')


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def timestamp(value):
    return dt.datetime.fromisoformat(value.replace('Z', '+00:00')).astimezone(dt.timezone.utc).isoformat()


def begin(cfg, agent, label, cohort=None, arm=None, output_budget=None, pair_key=None):
    if output_budget is not None and output_budget <= 0:
        raise UsageError('output budget must be positive')
    ident = 'window-' + uuid.uuid4().hex[:16]
    with Store(cfg) as st:
        st.conn.execute('INSERT INTO research_windows VALUES (?,?,?,?,?,?,?,?,?,?,?)',
                        (ident, agent, label, cohort, arm, 'active', now(), None, output_budget, None,
                         json.dumps({'pair_key': pair_key, 'budget_enforcement': 'observational'})))
    return ident


def window(cfg, ident):
    with Store(cfg) as st:
        row = st.conn.execute('SELECT * FROM research_windows WHERE id=?', (ident,)).fetchone()
    if row is None:
        raise UsageError(f'unknown research window {ident}')
    return dict(row)


def transition(cfg, ident, state, accepted=None):
    w = window(cfg, ident)
    if accepted is not None and accepted < 0:
        raise UsageError('accepted result count cannot be negative')
    allowed = {'active': {'paused', 'complete'}, 'paused': {'active', 'complete'}, 'complete': set()}
    if state not in allowed[w['status']]:
        raise UsageError(f"cannot change {w['status']} window to {state}")
    metadata = json.loads(w['metadata_json'])
    metadata.setdefault('events', []).append({'at': now(), 'status': state})
    if accepted is not None:
        metadata['outcome_count_source'] = 'operator_supplied; inspect proof receipts separately'
    with Store(cfg) as st:
        st.conn.execute('UPDATE research_windows SET status=?,ended_at=?,accepted_results=COALESCE(?,accepted_results),metadata_json=? WHERE id=?',
                        (state, now() if state == 'complete' else None, accepted, json.dumps(metadata), ident))


def ingest(cfg, source, window_id=None):
    path = Path(source).resolve()
    if not path.is_file():
        raise UsageError('usage source must be a local JSONL file')
    explicit = window(cfg, window_id) if window_id else None
    sid = None
    model = effort = None
    recorded = inserted = 0
    seen = {}
    sums = dict.fromkeys(FIELDS, 0)
    last_total = None
    last_at = None
    truncated = False
    active_window = None
    goal_number = 0
    end_pending = False
    observed_operations = set()
    with Store(cfg) as st:
        for lineno, line in enumerate(path.open(), 1):
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                # A writer may still be appending the last line. Malformed middle lines
                # leave coverage partial rather than silently becoming zero usage.
                truncated = True
                continue
            p = event.get('payload') or {}
            typ = event.get('type')
            if typ == 'session_meta' and sid is None:
                sid = p.get('id')
            if typ == 'turn_context':
                model, effort = p.get('model'), p.get('effort')
            if typ == 'response_item' and p.get('type') in ('custom_tool_call', 'function_call'):
                raw = str(p.get('input', p.get('arguments', '')))
                observed_operations.update(re.findall(r'\bop-[0-9a-f]{16}\b',raw))
                if 'tools.create_goal(' in raw:
                    goal_number += 1
                    active_window = f'import-{sid}-{goal_number}'
                    st.conn.execute('INSERT OR IGNORE INTO research_windows VALUES (?,?,?,?,?,?,?,?,?,?,?)',
                                    (active_window, sid or 'unknown', f'Imported goal {goal_number}', None,
                                     'historical', 'active', timestamp(event['timestamp']), None, None, None,
                                     json.dumps({'source': str(path), 'boundary': 'goal-tool-call'})))
                if 'tools.update_goal(' in raw and re.search(r'''["']?status["']?\s*:\s*["']complete["']''',raw):
                    end_pending = True
            if typ != 'token_usage_record' or p.get('thread_id') != sid:
                continue
            ident = p['response_id']
            u = {k: p.get('usage', {}).get(k) for k in FIELDS}
            if any(not isinstance(v, int) or isinstance(v, bool) or v < 0 for v in u.values()):
                raise UsageError(f'invalid/missing usage at line {lineno}')
            if u['cached_input_tokens'] > u['input_tokens'] or u['reasoning_output_tokens'] > u['output_tokens']:
                raise UsageError(f'inconsistent subset fields at line {lineno}')
            if ident in seen:
                if seen[ident] != u:
                    raise UsageError(f'conflicting duplicate usage at line {lineno}')
                continue
            seen[ident] = u
            at = timestamp(event['timestamp'])
            assigned = active_window
            association = 'imported_goal_boundary' if assigned else 'unassigned'
            if explicit and timestamp(explicit['started_at']) <= at and (not explicit['ended_at'] or at <= timestamp(explicit['ended_at'])):
                assigned, association = window_id, 'explicit_window_time_bounds'
            old = st.conn.execute('SELECT * FROM usage_records WHERE provider=? AND session_id=? AND response_id=?',
                                  ('codex', sid, ident)).fetchone()
            if old and any(old[k] != u[k] for k in FIELDS):
                raise UsageError(f'conflicting usage for response {ident}; no overwrite performed')
            if not old:
                operation_id = next(iter(observed_operations)) if len(observed_operations)==1 else None
                if operation_id and not st.conn.execute('SELECT 1 FROM operations WHERE id=?',(operation_id,)).fetchone(): operation_id=None
                st.conn.execute('INSERT INTO usage_records VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)',
                                ('codex', sid, ident, at, *[u[k] for k in FIELDS], model, effort,
                                 assigned, operation_id, association + ('; single operation ID observed in tool call' if operation_id else ''), str(path), lineno))
                inserted += 1
            elif explicit and assigned == window_id:
                if old['window_id'] not in (None, window_id) and not old['window_id'].startswith('import-'):
                    raise UsageError('response already assigned to another explicit window')
                st.conn.execute('UPDATE usage_records SET window_id=?,association=? WHERE provider=? AND session_id=? AND response_id=?',
                                (assigned, association, 'codex', sid, ident))
            recorded += 1
            observed_operations.clear()
            for k in FIELDS:
                sums[k] += u[k]
            last_total = p.get('thread_token_usage')
            last_at = at
            if end_pending and active_window:
                st.conn.execute('UPDATE research_windows SET status=?,ended_at=? WHERE id=?', ('complete', at, active_window))
                active_window, end_pending = None, False
        delta = {k: sums[k] - last_total.get(k, 0) for k in FIELDS} if last_total else None
        report = {'source': str(path), 'session_id': sid, 'records': recorded, 'inserted': inserted,
                  'usage': sums, 'last_record_at': last_at, 'reconciliation_delta': delta,
                  'coverage': 'reconciled_snapshot' if delta is not None and not any(delta.values()) and not truncated else 'partial',
                  'snapshot_caveat': 'Only recorded requests; an active request and later reporting may not yet be included.'}
        st.conn.execute('INSERT OR REPLACE INTO usage_imports VALUES (?,?,?,?,?)',
                        (str(path), path.stat().st_size, recorded, json.dumps(report), time.time()))
    return report


def report(cfg, ident=None):
    w = window(cfg, ident) if ident else None
    with Store(cfg) as st:
        rows = st.conn.execute('SELECT * FROM usage_records' + (' WHERE window_id=?' if ident else ''),
                               (ident,) if ident else ()).fetchall()
        imports = [json.loads(r[0]) for r in st.conn.execute('SELECT report_json FROM usage_imports')]
        paths = {r['source_path'] for r in rows}
        imports = [r for r in imports if r['source'] in paths]
        resources = dict(st.conn.execute('SELECT COUNT(*) AS jobs, SUM(seconds) AS worker_seconds, MAX(peak_mib) AS maximum_job_peak_mib FROM jobs' + (' WHERE operation_id IN (SELECT id FROM operations WHERE window_id=?)' if ident else ''),(ident,) if ident else ()).fetchone())
        metrics = dict(st.conn.execute('SELECT COUNT(*) AS calls,SUM(full_bytes) AS full_bytes,SUM(returned_bytes) AS returned_bytes FROM tool_metrics' + (' WHERE window_id=?' if ident else ''),(ident,) if ident else ()).fetchone())
    totals = {k: sum(r[k] for r in rows) for k in FIELDS}
    totals['uncached_input_tokens'] = totals['input_tokens'] - totals['cached_input_tokens']
    exceeded = bool(w and w['output_budget'] and totals['output_tokens'] > w['output_budget']) if rows else None
    if not rows: totals = dict.fromkeys(totals,None)
    return {'window': w, 'responses': len(rows), 'usage': totals,
            'coverage': 'no_records' if not rows else 'recorded_snapshot',
            'imports': imports, 'resources':resources, 'tool_results':metrics,
            'resource_coverage':'Only jobs explicitly linked to the window; unlinked work is not included.' if ident else 'All recorded project jobs; historical resource fields may be missing.',
            'operation_associations': 'A unique operation ID observed in a tool call associates the whole response; it does not causally allocate reasoning.',
            'output_budget_exceeded': exceeded,
            'budget_enforcement': 'observational; does not control client request admission'}


def compare(cfg, baseline_ids, treatment_ids, future_units=1, setup_ids=None):
    if not baseline_ids or len(baseline_ids) != len(treatment_ids) or future_units < 0:
        raise UsageError('provide equally sized nonempty matched window lists and nonnegative future units')
    all_ids = baseline_ids + treatment_ids + (setup_ids or [])
    if len(set(all_ids)) != len(all_ids):
        raise UsageError('comparison windows must be distinct; setup cannot overlap evaluated windows')
    pairs = []
    for a, b in zip(baseline_ids, treatment_ids):
        ra, rb = report(cfg, a), report(cfg, b)
        wa, wb = ra['window'], rb['window']
        ma, mb = json.loads(wa['metadata_json']), json.loads(wb['metadata_json'])
        if wa['status'] != 'complete' or wb['status'] != 'complete' or not ra['responses'] or not rb['responses']:
            raise UsageError('both windows must be complete and contain imported usage')
        if any(i.get('coverage') != 'reconciled_snapshot' for i in ra['imports']+rb['imports']):
            raise UsageError('source snapshots must reconcile before estimating savings')
        if not wa['cohort'] or wa['cohort'] != wb['cohort'] or not ma.get('pair_key') or ma.get('pair_key') != mb.get('pair_key'):
            raise UsageError('matched windows need the same nonempty cohort and pair key')
        if wa['accepted_results'] is None or wa['accepted_results'] != wb['accepted_results']:
            raise UsageError('record equal verified outcome counts before estimating savings')
        pairs.append({'baseline': a, 'treatment': b, 'outcomes': wa['accepted_results'],
                      'baseline_usage': ra['usage'], 'treatment_usage': rb['usage'],
                      'saved': {k: ra['usage'][k] - rb['usage'][k] for k in ra['usage']}})
    setup_reports = [report(cfg,w) for w in (setup_ids or [])]
    if any(r['window']['status']!='complete' or not r['responses'] or any(i.get('coverage')!='reconciled_snapshot' for i in r['imports']) for r in setup_reports):
        raise UsageError('setup windows must be complete and have reconciled recorded usage')
    setup = {k: sum(r['usage'][k] for r in setup_reports) for k in pairs[0]['saved']}
    mean = {k: statistics.mean(p['saved'][k] for p in pairs) for k in setup}
    baseline = {k: statistics.mean(p['baseline_usage'][k] for p in pairs) for k in setup}
    return {'pairs': pairs, 'matched_pairs': len(pairs), 'mean_saved_per_window': mean,
            'percent_saved': {k: 100 * mean[k] / baseline[k] if baseline[k] else None for k in mean},
            'observed_output_saving_range': [min(p['saved']['output_tokens'] for p in pairs), max(p['saved']['output_tokens'] for p in pairs)],
            'setup_usage': setup if setup_ids else None, 'setup_coverage':'recorded' if setup_ids else 'not_provided', 'future_windows': future_units,
            'estimated_recurring_saved':{k:future_units*mean[k] for k in mean},
            'estimated_net_saved': {k: future_units * mean[k] - setup[k] for k in mean} if setup_ids else None,
            'output_break_even_windows': math.ceil(setup['output_tokens'] / mean['output_tokens']) if setup_ids and mean['output_tokens'] > 0 else None,
            'limitations': ['Projection assumes future windows resemble the matched cohort.',
                           'Outcome counts are operator supplied; compare actual proof receipts.',
                           'Recorded usage may lag; include failed work, setup and reporting.',
                           'Field-wise token estimate, not a dollar or weekly-allowance estimate.',
                           'Observed range is not a confidence interval.']}
