"""Commands for ordinary-code run monitoring and human-readable progress."""
import json
import time

from es.errors import UsageError
from es.output import Result
from es.spec import Arg, CommandSpec, command


def watch(ctx, out):
    from es import run_monitor
    r = run_monitor.register(ctx.cfg, out, ctx.agent)
    return Result(0, r, [f"Registered {r['monitor_id']}; es worker observes without model polling.",
                         r['callback_required']])


def progress(ctx, out, follow=0):
    from es import run_monitor
    if not 0 <= follow <= 55:
        raise UsageError('follow must be zero through 55 seconds')
    deadline = time.monotonic() + follow
    previous = None
    while True:
        r = run_monitor.progress(ctx.cfg, out)
        line = (f"{r['status']} / host {r['host_status']}; {r['remaining_seconds']}s remaining; "
                f"jobs {json.dumps(r['jobs'], sort_keys=True)}; "
                f"peak {r['max_job_peak_mib']} MiB; results reported {r['accepted_results_reported']}")
        if not follow or r['host_terminal'] or time.monotonic() >= deadline:
            return Result(0, r, [line])
        if line != previous:
            print(line, flush=True)
            previous = line
        time.sleep(min(5, max(0, deadline - time.monotonic())))


def observe(ctx):
    from es import run_monitor
    return Result(0, run_monitor.tick(ctx.cfg), ['Observer tick complete.'])


def unwatch(ctx, out):
    from es import run_monitor
    return Result(0, run_monitor.pause(ctx.cfg, out, ctx.agent), ['Monitor paused; research continues.'])


command(CommandSpec('run_watch', ['run', 'watch'], 'Register durable run-level monitoring with the worker.', watch,
                    [Arg('out', 'recorded run output directory', positional=True, required=True)]))
command(CommandSpec('run_progress', ['run', 'progress'], 'Read run progress without calling a model.', progress,
                    [Arg('out', 'recorded run output directory', positional=True, required=True),
                     Arg('follow', 'stream status for up to 55 seconds', 'int', default=0)]))
command(CommandSpec('run_observe', ['run', 'observe'], 'Run one deterministic observer tick.',
                    observe))
command(CommandSpec('run_unwatch', ['run', 'unwatch'], 'Pause observer delivery without cancelling research.',
                    unwatch,
                    [Arg('out', 'recorded run output directory', positional=True, required=True)]))
