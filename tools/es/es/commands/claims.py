from __future__ import annotations

import time

from es import EXIT_CHECK_FAILED, EXIT_OK
from es.context import Ctx
from es.errors import CheckFailed
from es.nodes import find_node, load_nodes_json, nodes_from_json
from es.output import Result
from es.spec import Arg, CommandSpec, command
from es.store import Store


def run_claim(ctx: Ctx, name: str, agent: str | None = None, note: str | None = None, force: bool = False) -> Result:
    cfg = ctx.cfg
    agent = agent or ctx.agent
    n = find_node(cfg, name)
    with Store(cfg) as st:
        existing = st.claims().get(n.name)
        if existing and existing["agent"] != agent:
            raise CheckFailed(f"{n.name} is claimed by {existing['agent']} until {time.strftime('%Y-%m-%d %H:%M', time.localtime(existing['expires_at']))}")
        if n.status == "proposed" and n.kind == "conjecture":
            raise CheckFailed(f"{n.name} is a conjecture whose falsifier has not passed; run `es falsify {n.short}` first")
        if not n.ready and not existing:
            why = "blocked by " + ", ".join(n.blocked_by) if n.blocked_by else f"status {n.status}"
            if not force:
                raise CheckFailed(f"{n.name} is not ready ({why}); use --force to claim anyway")
            st.event("claim-forced", n.name, agent, why)
        claim = st.claim(n.name, agent, cfg.claim_ttl_hours, note)
    return Result(EXIT_OK, {"claim": claim}, [f"claimed {n.name} for {agent} until {time.strftime('%Y-%m-%d %H:%M', time.localtime(claim['expires_at']))}"])


def run_release(ctx: Ctx, name: str, agent: str | None = None, outcome: str = "abandoned") -> Result:
    cfg = ctx.cfg
    n = find_node(cfg, name)
    with Store(cfg) as st:
        ok = st.release(n.name, agent or ctx.agent, outcome=outcome)
    if not ok:
        return Result(EXIT_CHECK_FAILED, {"released": False}, [f"{n.name} was not claimed"])
    return Result(EXIT_OK, {"released": True}, [f"released {n.name} ({outcome})"])


command(CommandSpec(name="claim", cli=["claim"], help="Claim a ready node for this agent (12 h by default).", run=run_claim,
                    args=[Arg("name", "node name", positional=True, required=True), Arg("agent", "agent id (default: ES_AGENT)"),
                          Arg("note", "free text"), Arg("force", "claim a node that is not ready (logged)", "bool")]))
command(CommandSpec(name="release", cli=["release"], help="Release a claim.", run=run_release,
                    args=[Arg("name", "node name", positional=True, required=True), Arg("agent", "agent id"),
                          Arg("outcome", "abandoned | closed | refuted", default="abandoned", choices=["abandoned", "closed", "refuted"])]))
