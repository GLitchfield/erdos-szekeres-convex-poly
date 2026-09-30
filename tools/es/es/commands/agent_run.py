"""CLI registration for bounded Codex native-goal runs."""
from __future__ import annotations

from es.output import Result
from es.spec import Arg, CommandSpec, command


def run_agent(ctx, out, prompt=None, model=None, effort=None, hours=None, resume=False):
    from es.agent_run import submit_agent_run

    result = submit_agent_run(
        ctx.cfg,
        agent=ctx.agent,
        out=out,
        prompt=prompt,
        model=model,
        effort=effort,
        hours=hours,
        resume=resume,
    )
    job = result["job"]
    return Result(
        0,
        result,
        [f"queued native-goal host {job['id']} (2G) for {result['run']['out']}",
         f"monitor with `es run agent-status {result['run']['out']}` and `es job wait {job['id']}`"],
    )


def run_agent_status(ctx, out):
    from es.agent_run import status_agent_run

    state = status_agent_run(ctx.cfg, out)
    goal = (state.get("goal") or {}).get("status")
    suffix = f"; goal {goal}" if goal else ""
    remaining = state.get("remaining_seconds")
    if remaining is not None:
        suffix += f"; {remaining}s to research deadline"
    return Result(0, state, [f"{state['status']} ({state['phase']}){suffix}"])


def run_finish(ctx, out, note):
    from es.agent_run import request_finish

    result = request_finish(ctx.cfg, out, agent=ctx.agent, note=note)
    return Result(0, result, [f"finish requested for {result['out']}: the host ends research within a minute "
                              "and admits the single finalization turn (watch `es run agent-status`)"])


def run_review(ctx, out, artifact_root=None):
    from es.run_review import build_review

    result = build_review(ctx.cfg, out, artifact_root=artifact_root)
    counts = result.get("counts") or {}
    artifact = result.get("artifact") or {}
    return Result(
        0,
        result,
        [f"reviewed {out}: {counts.get('jobs', 0)} research jobs, "
         f"{counts.get('explicit_proof_receipts', 0)} explicit proof receipts; artifact {artifact.get('id', 'unavailable')}"]
    )


command(CommandSpec(
    "run_agent",
    ["run", "agent"],
    "Queue a 2G host for one bounded, durable Codex native-goal run.",
    run_agent,
    [
        Arg("out", "run directory under runs/ or data/", required=True),
        Arg("prompt", "UTF-8 objective file (required for a new run)"),
        Arg("model", "Codex model; new runs default to gpt-5.6-sol"),
        Arg("effort", "reasoning effort; new runs default to xhigh",
            choices=["none", "minimal", "low", "medium", "high", "xhigh", "max", "ultra"]),
        Arg("hours", "research hours; finite and positive, new runs default to 12", "float"),
        Arg("resume", "explicitly resume the frozen thread after a stopped host", "bool"),
    ],
))

command(CommandSpec(
    "run_agent_status",
    ["run", "agent-status"],
    "Read compact state for a Codex native-goal run without contacting the model.",
    run_agent_status,
    [Arg("out", "existing run directory under runs/ or data/", positional=True, required=True)],
))

command(CommandSpec(
    "run_review",
    ["run", "review"],
    "Create a bounded final review summary and immutable sanitized evidence for a native-goal run.",
    run_review,
    [Arg("out", "existing run directory under runs/ or data/", positional=True, required=True),
     Arg("artifact_root", "explicit run artifact root containing the host out directory")],
))

command(CommandSpec(
    "run_finish",
    ["run", "finish"],
    "End a native-goal run's research window early (its result is closed and reviewed): the host admits the finalization turn now and releases its reservation.",
    run_finish,
    [Arg("out", "existing run directory under runs/ or data/", positional=True, required=True),
     Arg("note", "the verified result that makes further research unnecessary", required=True)],
))
