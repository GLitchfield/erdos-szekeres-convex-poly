from __future__ import annotations

from es import EXIT_LEAN, EXIT_OK
from es.build import build as do_build
from es.context import Ctx
from es.output import Result
from es.spec import Arg, CommandSpec, command


def run(ctx: Ctx, target: str, name: str | None = None, budget: int | None = None, force: bool = False,
        serial: bool = False, no_serial: bool = False, async_: bool = False) -> Result:
    cfg = ctx.cfg
    if async_:
        from es.jobs import submit
        argv = ["build", target] + ([name] if name else []) + ([f"--budget={budget}"] if budget else [])
        job = submit(cfg, kind="build", node=name, argv=argv, agent=ctx.agent, budget_min=budget)
        return Result(EXIT_OK, {"job": job}, [f"submitted job {job['id']}"])
    if target == "core" and budget is None:
        budget = cfg.core_budget_min
    node_module = None
    if target == "node":
        from es.nodes import node_module_for
        node_module = node_module_for(cfg, name or "")
    ser = True if serial else (False if no_serial else None)
    results = do_build(cfg, target, budget_min=budget, node_module=node_module, force=force, serial=ser)
    res = Result()
    for r in results:
        res.line(f"{' '.join(r.command)}: {r.summary()}")
    last = results[-1]
    res.exit_code = EXIT_OK if all(r.ok for r in results) else EXIT_LEAN
    if res.exit_code != EXIT_OK:
        res.line("--- log tail ---")
        res.human.extend(last.tail)
    res.payload = {
        "results": [r.__dict__ for r in results],
        "seconds": sum(r.seconds for r in results),
        "built": sum(r.built for r in results),
    }
    return res


command(
    CommandSpec(
        name="build",
        cli=["build"],
        help="Wrap `lake build` with a memory guard, a wall-clock budget, and a summary line.",
        run=run,
        long_running=True,
        args=[
            Arg("target", "core | blueprint | certs | node", positional=True, required=True, choices=["core", "blueprint", "certs", "node"]),
            Arg("name", "node name (for target=node)", positional=True),
            Arg("budget", "wall-clock budget in minutes", "int"),
            Arg("force", "run even if another lean compiler is running", "bool"),
            Arg("serial", "build missing-olean modules one at a time first (default from config)", "bool"),
            Arg("no_serial", "skip the serial pre-pass", "bool"),
            Arg("async_", "submit as a background job and return its id", "bool"),
        ],
    )
)
