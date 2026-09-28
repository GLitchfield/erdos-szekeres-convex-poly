from __future__ import annotations

import time

from es import EXIT_LEAN, EXIT_OK
from es.build import run_guarded
from es.context import Ctx
from es.nodes import find_node
from es.output import Result
from es.spec import Arg, CommandSpec, command
from es.store import Store


def run(ctx: Ctx, name: str, budget: int | None = None, async_: bool = False, force: bool = False,
        targeted: bool = False) -> Result:
    cfg = ctx.cfg
    n = find_node(cfg, name)
    if async_:
        from es.jobs import submit
        argv = ["check", n.name] + ([f"--budget={budget}"] if budget else [])
        if targeted:
            argv.append("--targeted")
        job = submit(cfg, kind="check", node=n.name, argv=argv, agent=ctx.agent, budget_min=budget)
        return Result(EXIT_OK, {"job": job}, [f"submitted job {job['id']}"])
    log = cfg.build_log_dir / f"check-{time.strftime('%Y%m%d-%H%M%S')}-{n.short}.log"
    started = time.time()
    build = run_guarded(cfg, [cfg.lake, "build", n.module], log_path=log, budget_min=budget, force=force)
    res = Result()
    res.line(f"lake build {n.module}: {build.summary()}")
    if not build.ok:
        res.human.extend(build.tail)
        res.exit_code = EXIT_LEAN
        res.payload = {"node": n.name, "build": build.__dict__}
        with Store(cfg) as st:
            st.event("check-failed", n.name, ctx.agent, {"seconds": build.seconds})
        return res
    from es.commands.extract import run_extract
    from es.commands.node import targeted_extract
    from es.errors import Refused

    from es.commands.extract import NeedsFullExtract, run_incremental

    incremental = False

    def closure_only() -> tuple[dict, list, list[str]]:
        # Re-extract the blueprint modules whose inputs changed (this one included) and merge
        # them into the index; without a fingerprinted base, judge the node from its closure only.
        nonlocal incremental
        try:
            out = run_incremental(ctx, force=force, extra_modules=[n.module])
            incremental = True
            return out
        except NeedsFullExtract as exc:
            res.line(f"incremental index update unavailable ({exc})")
            return targeted_extract(ctx, n.module)

    if targeted:
        payload, index, problems = closure_only()
    else:
        try:
            payload, index, problems = run_extract(ctx, force=force)
        except Refused as exc:
            # The full extractor cannot start (memory): judge the node from its import closure.
            res.line(f"full extract refused ({exc}); targeted extract of {n.module}")
            payload, index, problems = closure_only()
            targeted = True
    node = next((x for x in payload["nodes"] if x["name"] == n.name), None)
    if node is None:
        res.line(f"{n.name} not found after extract")
        res.exit_code = EXIT_LEAN
        return res
    res.line(f"{n.name}: sorry={node['sorry']} status={node['status']} axioms={', '.join(node['axioms']) or '-'}"
             + (f" uncovered={', '.join(node['uncovered_axioms'])}" if node["uncovered_axioms"] else ""))
    if node["deps_declared"] and set(node["deps_actual"]) != set(node["deps_declared"]):
        res.line(f"  declared deps differ from actual: declared {node['deps_declared']}, actual {node['deps_actual']}")
    with Store(cfg) as st:
        outcome = "closed" if node["status"] == "closed" else ("proved-unallowlisted" if node["status"] == "unallowlisted" else "checked")
        st.event("check", n.name, ctx.agent, {"outcome": outcome, "seconds": time.time() - started})
        if node["status"] == "closed":
            st.record_attempt(n.name, ctx.agent, "closed", note="es check")
    if targeted and incremental:
        inc = payload.get("_incremental", {})
        res.line(f"nodes.json/status.md updated incrementally ({len(inc.get('reextracted', []))} module(s) re-extracted)")
    elif targeted:
        res.line("targeted extract: nodes.json/status.md not updated; run `es extract` when memory allows")
    res.payload = {"node": node, "build_seconds": build.seconds, "build_peak_mib": build.peak_mib,
                   "setup_cleanup": getattr(build, "setup_cleanup", None), "targeted": targeted,
                   "incremental": incremental}
    res.exit_code = EXIT_OK
    return res


command(CommandSpec(name="check", cli=["check"], long_running=True,
                    help="Build only the node's module, re-extract, and report sorry-free / axioms / build time.", run=run,
                    args=[Arg("name", "node name", positional=True, required=True), Arg("budget", "wall-clock budget in minutes", "int"),
                          Arg("async_", "submit as a background job", "bool"), Arg("force", "run even if another lean compiler is running", "bool"),
                          Arg("targeted", "extract only this node's import closure; do not rewrite the full index", "bool")]))
