from __future__ import annotations

from es import usage
from es.output import Result
from es.spec import Arg, CommandSpec, command


def sync(ctx, window=None):
    import os
    from pathlib import Path
    from es.errors import UsageError
    session=os.environ.get('CODEX_THREAD_ID')
    if not session: raise UsageError('no CODEX_THREAD_ID; use usage import with the explicit session JSONL')
    paths=list((Path.home()/'.codex/sessions').glob('*/*/*/*'+session+'*.jsonl'))
    if len(paths)!=1: raise UsageError('no unique current session JSONL; use usage import with an explicit path')
    return ingest(ctx,str(paths[0]),window or os.environ.get('ES_WINDOW_ID'))


def ingest(ctx, source, window=None):
    r = usage.ingest(ctx.cfg, source, window)
    return Result(0, r, [f"imported {r['inserted']} new responses; {r['coverage']}"])


def report(ctx, window=None):
    r = usage.report(ctx.cfg, window)
    message = f"{r['responses']} responses; {r['usage']['output_tokens']:,} output tokens; {r['coverage']}" if r['responses'] else 'No usage records; token consumption is unknown.'
    return Result(0, r, [message])


def compare(ctx, baseline, treatment, future=1, setup=None):
    r = usage.compare(ctx.cfg, baseline, treatment, future, setup)
    return Result(0, r, [f"{r['matched_pairs']} matched pairs; mean output saving {r['mean_saved_per_window']['output_tokens']:,.0f}; break-even {r['output_break_even_windows']}"])


def begin(ctx, label, cohort=None, arm=None, budget=None, pair_key=None):
    ident = usage.begin(ctx.cfg, ctx.agent, label, cohort, arm, budget, pair_key)
    return Result(0, {'window_id': ident, 'budget_enforcement': 'observational'}, [ident])


def change(ctx, id, state, accepted=None):
    usage.transition(ctx.cfg, id, state, accepted)
    return Result(0, {'window_id': id, 'status': state}, [f'{id}: {state}'])


command(CommandSpec('usage_import', ['usage', 'import'], 'Import exact Codex usage from local JSONL; no conversation text is stored.', ingest,
                    [Arg('source', 'JSONL source', positional=True, required=True), Arg('window', 'explicit window ID')]))
command(CommandSpec('usage_sync',['usage','sync'],'Import currently recorded usage for CODEX_THREAD_ID; active responses may lag.',sync,[Arg('window','explicit research/setup window ID')]))
command(CommandSpec('usage_report', ['usage', 'report'], 'Recorded usage, coverage and observational budget status.', report, [Arg('window', 'window ID')]))
command(CommandSpec('usage_compare', ['usage', 'compare'], 'Estimate future savings and setup break-even from matched completed windows.', compare,
                    [Arg('baseline', 'matched baseline IDs in order', 'list', required=True), Arg('treatment', 'matched treatment IDs in order', 'list', required=True),
                     Arg('future', 'future comparable windows', 'int', default=1), Arg('setup', 'separate implementation/setup window IDs', 'list')]))
command(CommandSpec('run_begin', ['run', 'begin'], 'Record a research window; does not create a model goal.', begin,
                    [Arg('label', 'window label', positional=True, required=True), Arg('cohort', 'comparison cohort'), Arg('arm', 'baseline/treatment/setup'),
                     Arg('budget', 'observational output-token budget', 'int'), Arg('pair_key', 'matched task/source identity')]))
for action, state in [('pause', 'paused'), ('resume', 'active'), ('end', 'complete')]:
    def handler(ctx, id, accepted=None, _state=state):
        return change(ctx, id, _state, accepted)
    command(CommandSpec('run_' + action, ['run', action], f'Mark research window {state}.', handler,
                        [Arg('id', 'window ID', positional=True, required=True), Arg('accepted', 'checked result count with receipts', 'int')]))
command(CommandSpec('run_report', ['run', 'report'], 'Generate a factual usage handoff for a research window.', report, [Arg('window', 'window ID', required=True)]))
def handoff(ctx, window):
    from es.bundles import handoff as generate
    from es.commands.automation import result
    return result(ctx, generate(ctx.cfg,window))
command(CommandSpec('run_handoff',['run','handoff'],'Generate a factual resume bundle from recorded work and usage.',handoff,[Arg('window','window ID',required=True)]))
