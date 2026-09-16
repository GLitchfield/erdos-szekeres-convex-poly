"""Deterministic run supervision; normal polling never calls a language model."""
from __future__ import annotations

from collections import Counter
import fcntl
import hashlib
import json
from pathlib import Path
import time

from es.agent_run import _output, _read_state, _parse_utc, LIVE_JOB_STATES
from es.config import load_config, primary_root
from es.errors import UsageError
from es.store import Store

PREFIX = 'run-monitor:'
TERMINAL_JOBS = {'done', 'failed', 'killed'}


def _key(out):
    return PREFIX + hashlib.sha256(str(out).encode()).hexdigest()[:24]


def _save(cfg, key, value):
    with Store(cfg) as st:
        st.conn.execute('INSERT OR REPLACE INTO automation_meta VALUES (?,?)',
                        (key, json.dumps(value, sort_keys=True)))


def _load(cfg, key):
    with Store(cfg) as st:
        row = st.conn.execute('SELECT value FROM automation_meta WHERE key=?', (key,)).fetchone()
    return json.loads(row[0]) if row else None


def register(cfg, out, agent):
    path, _ = _output(cfg, out)
    state = _read_state(path)
    if Path(state['root']).resolve() != cfg.root.resolve() or Path(state['out']).resolve() != path:
        raise UsageError('monitor must use the recorded run root and output directory')
    if state.get('coordinator_agent', agent) != agent:
        raise UsageError('monitor belongs to the recorded coordinator')
    key = _key(path)
    old = _load(cfg, key)
    if old and old['agent'] != agent:
        raise UsageError('run already has a different coordinator')
    record = old or {'root': str(cfg.root.resolve()), 'out': str(path), 'agent': agent,
                     'created_at': time.time(), 'signals': [], 'capacity_retries': []}
    record['enabled'] = True
    _save(cfg, key, record)
    return {'monitor_id': key, 'observing': True, 'idle_model_requests': 0,
            'coordinator_output_target': cfg.get('automation', 'monitor', 'coordinator_output_target', default=10000),
            'budget_enforcement': 'observational; record monitoring and final review in separate usage windows',
            'callback_required': 'A verified delivery binding is required before ending the reporting turn.'}


def progress(cfg, out):
    """Small status projection from durable state and jobs, without model requests."""
    path, _ = _output(cfg, out)
    state = _read_state(path)
    if Path(state['root']).resolve() != cfg.root.resolve() or Path(state['out']).resolve() != path:
        raise UsageError('progress must use the recorded run root and output directory')
    with Store(cfg) as st:
        host = st.job(state.get('current_host_job_id', ''))
        jobs = [dict(r) for r in st.conn.execute(
            'SELECT id,status,memory_max,peak_mib FROM jobs WHERE agent=?',
            (state.get('researcher_agent', ''),))]
        window = st.conn.execute('SELECT accepted_results FROM research_windows WHERE id=?',
                                 (state.get('window_id'),)).fetchone()
    timing = state.get('timing') or {}
    deadline = timing.get('deadline_at')
    remaining = max(0, round(_parse_utc(deadline) - time.time())) if deadline else None
    active = [j for j in jobs if j['status'] in LIVE_JOB_STATES]
    return {'schema_version': 1, 'run_id': _key(path), 'status': state.get('status'),
            'phase': state.get('phase'), 'goal_status': (state.get('goal') or {}).get('status'),
            'host_job_id': host['id'] if host else state.get('current_host_job_id'),
            'host_status': host['status'] if host else 'missing',
            'host_terminal': bool(host and host['status'] in TERMINAL_JOBS),
            'remaining_seconds': remaining, 'deadline_at': deadline,
            'jobs': dict(Counter(j['status'] for j in jobs)),
            'active_jobs': active[:8], 'active_jobs_total': len(active),
            'max_job_peak_mib': max((j['peak_mib'] or 0 for j in jobs), default=0),
            'accepted_results_reported': window[0] if window else None,
            'theorem_credit': 'inspect compiled proof receipts', 'model_requests': 0}


def _capacity_retry(cfg, record, state, host, now):
    """Admit only a bounded capacity retry. The resumed host rechecks fresh evidence."""
    cap = cfg.get('automation', 'monitor', 'provider_capacity_retries', default=0)
    if not isinstance(cap, int) or isinstance(cap, bool) or not 0 <= cap <= 3:
        raise UsageError('provider_capacity_retries must be an integer from zero to three')
    attempts = record['capacity_retries']
    previous = next((a for a in attempts if a['host_job_id'] == host['id']), None)
    if previous:
        return previous.get('status') == 'submitted'
    p = state.get('progress') or {}
    goal = state.get('goal') or {}
    completed = p.get('last_turn_completed_at')
    updated = goal.get('updatedAt')
    eligible = (len(attempts) < cap and host['status'] == 'failed'
                and not host.get('cancel_requested')
                and state.get('status') == 'goal_blocked' and goal.get('status') == 'blocked'
                and p.get('last_turn_status') == 'failed'
                and p.get('last_turn_error_code') == 'serverOverloaded'
                and isinstance(completed, (float, int)) and not isinstance(completed, bool)
                and isinstance(updated, (float, int)) and not isinstance(updated, bool)
                and completed >= updated
                and now < _parse_utc(state['timing']['deadline_at']))
    if not eligible:
        return False
    from es.agent_run import submit_agent_run
    attempt = {'host_job_id': host['id'], 'status': 'pending', 'at': now}
    attempts.append(attempt)
    # Persist intent before submission. A crash must never blindly repeat the effect.
    _save(cfg, _key(Path(record['out'])), record)
    try:
        submitted = submit_agent_run(cfg, agent=record['agent'], out=record['out'], resume=True, capacity_only=True)
    except Exception as exc:
        attempt.update(status='needs_reconciliation', error_type=type(exc).__name__)
        _save(cfg, _key(Path(record['out'])), record)
        return False
    attempt.update(status='submitted', new_host_job_id=submitted['job']['id'])
    _save(cfg, _key(Path(record['out'])), record)
    return True


def _observe(cfg, key, record, now):
    from es import run_delivery

    def flush_signal():
        pending = record.get('pending_signal')
        if pending:
            run_delivery.emit(cfg, record['agent'], pending['event_id'], pending['payload'])
            if pending['signal'] not in record['signals']:
                record['signals'].append(pending['signal'])
            record['last_event_id'] = pending['event_id']
            record.pop('pending_signal')
            _save(cfg, key, record)

    # Replay the same immutable payload after a crash between outbox insertion
    # and recording the signal. Rebuilding a review would change its timestamp.
    flush_signal()
    path, _ = _output(cfg, record['out'])
    state = _read_state(path)
    snapshot = progress(cfg, path)
    with Store(cfg) as st:
        host = st.job(state.get('current_host_job_id', ''))
    # An observer never decides a mathematical blocker from quiet output or elapsed
    # compiler time. Ordinary child-job failures stay with the research agent.
    reason = None
    with Store(cfg) as st:
        unknown = [r[0] for r in st.conn.execute(
            "SELECT id FROM jobs WHERE agent=? AND status='unknown_execution'",
            (state.get('researcher_agent', ''),))]
    if host and host['status'] == 'unknown_execution':
        unknown.append(host['id'])
    if unknown:
        since = record.setdefault('unknown_since', now)
        delay = max(0, cfg.get('automation', 'monitor', 'unknown_execution_grace_seconds', default=60))
        if now - since >= delay:
            from es.resources import reconcile
            result = reconcile(cfg)  # only definite stopped scopes release capacity
            unknown = [ident for ident in unknown if ident in result['unknown_execution']]
            if unknown:
                reason = 'infrastructure_blocked'
    else:
        record.pop('unknown_since', None)
    if host and host['status'] in TERMINAL_JOBS:
        if _capacity_retry(cfg, record, state, host, now):
            record['snapshot'] = snapshot
            _save(cfg, key, record)
            return {'run_id': key, 'status': 'capacity_retry_submitted', 'model_requests': 0}
        reason = 'host_stopped_with_pending_jobs' if snapshot['active_jobs_total'] else 'run_terminal'
    if not host:
        reason = 'host_receipt_missing'
    # One signal per host generation and unresolved scope set. Changed token counters,
    # theorem counts, and routine Lean failures never produce coordinator events.
    signal = None
    if reason:
        signal = hashlib.sha256(json.dumps([snapshot['host_job_id'], reason, sorted(unknown)],
                                          sort_keys=True).encode()).hexdigest()[:24]
    if signal and signal not in record['signals']:
        payload = {'type': 'run_terminal' if reason == 'run_terminal' else 'infrastructure_blocked',
                   'reason': reason, 'run': key, 'status': snapshot['status'],
                   'job_id': snapshot['host_job_id'], 'host_status': snapshot['host_status'],
                   'jobs': snapshot['jobs'], 'accepted_results_reported': snapshot['accepted_results_reported'],
                   'unresolved_job_ids': unknown[:8], 'theorem_credit': 'not_inferred'}
        if reason == 'run_terminal':
            try:
                from es.run_review import build_review
                payload['review'] = build_review(cfg, path)
            except Exception as exc:
                payload['review_error_type'] = type(exc).__name__
        event_id = key + ':' + signal
        record['pending_signal'] = {'signal': signal, 'event_id': event_id, 'payload': payload}
        _save(cfg, key, record)
        flush_signal()
    record['snapshot'] = snapshot
    record['updated_at'] = now
    _save(cfg, key, record)
    delivery = run_delivery.dispatch(cfg, record['agent'])
    if (reason == 'run_terminal' and delivery.get('event_id') == record.get('last_event_id')
            and delivery.get('status') in {'queued', 'delivered'}):
        record['enabled'] = False
        _save(cfg, key, record)
    return {'run_id': key, 'status': reason or 'observing', 'delivery': delivery,
            'model_requests': delivery.get('model_requests', 0)}


def tick(cfg):
    """Worker hook. A filesystem lock serializes observers across worker processes."""
    lock = cfg.db_path.parent / 'run-monitor.lock'
    lock.parent.mkdir(parents=True, exist_ok=True)
    with lock.open('a+') as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return {'status': 'observer_busy', 'model_requests': 0}
        with Store(cfg) as st:
            records = [(r[0], json.loads(r[1])) for r in st.conn.execute(
                'SELECT key,value FROM automation_meta WHERE key LIKE ?', (PREFIX + '%',))]
        results = []
        for key, record in records:
            if not record.get('enabled'):
                continue
            try:
                run_cfg = load_config(Path(record['root']))
                if primary_root(run_cfg.root).resolve() != primary_root(cfg.root).resolve():
                    raise UsageError('monitor record points outside the shared checkout')
                results.append(_observe(run_cfg, key, record, time.time()))
            except Exception as exc:
                # A broken observer cannot stop the worker or spam paid retries.
                record['observer_error_type'] = type(exc).__name__
                _save(cfg, key, record)
                delivery = {}
                try:
                    from es import run_delivery
                    run_delivery.emit(cfg, record['agent'], key + ':observer-error:' + type(exc).__name__,
                                      {'type': 'infrastructure_blocked', 'run': key,
                                       'reason': 'observer_error', 'summary': type(exc).__name__})
                    delivery = run_delivery.dispatch(cfg, record['agent'])
                except Exception:
                    pass  # Durable error remains visible even if delivery transport is down.
                results.append({'run_id': key, 'status': 'observer_error', 'error_type': type(exc).__name__,
                                'model_requests': delivery.get('model_requests', 0)})
        return {'runs': results, 'model_requests': sum(r.get('model_requests', 0) for r in results)}


def pause(cfg, out, agent):
    path, _ = _output(cfg, out)
    key = _key(path)
    record = _load(cfg, key)
    if not record or record['agent'] != agent:
        raise UsageError('no monitor owned by this coordinator')
    record['enabled'] = False
    _save(cfg, key, record)
    return {'monitor_id': key, 'paused': True, 'compute_cancelled': False}
