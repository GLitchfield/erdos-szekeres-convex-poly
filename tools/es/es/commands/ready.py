from __future__ import annotations

from es import EXIT_OK
from es.context import Ctx
from es.nodes import days_open
from es.output import Result, table
from es.spec import Arg, CommandSpec, command
from es.store import Store


def run(ctx: Ctx, ws: str | None = None, kind: str | None = None) -> Result:
    cfg = ctx.cfg
    from es.commands.status import load_live
    with Store(cfg) as st:
        claims = st.claims()
    data, nodes, _dests = load_live(cfg, claims)
    out = []
    for n in nodes:
        if claims.get(n.name):
            continue
        if not n.ready:
            continue
        if ws and n.ws != ws:
            continue
        if kind and n.kind != kind:
            continue
        out.append(n)
    from es.commands.status import stale_lines
    res = Result()
    for line in stale_lines(cfg, nodes):
        res.line(line)
    if not out:
        res.line("no ready nodes")
    res.human.extend(table([[n.ws, n.name, n.kind, days_open(n.opened), n.consumer or n.tags.get("dangling-ok", "")] for n in out], ["ws", "node", "kind", "days", "consumer"]))
    res.payload = {"ready": [n.to_json() for n in out]}
    res.exit_code = EXIT_OK
    return res


command(
    CommandSpec(
        name="ready",
        cli=["ready"],
        help="Open, unclaimed nodes whose declared and Lean dependencies are closed (and whose falsifier passed, for conjectures).",
        run=run,
        args=[Arg("ws", "only this workstream"), Arg("kind", "only this kind", choices=["formalization", "conjecture", "refutation"])],
    )
)
