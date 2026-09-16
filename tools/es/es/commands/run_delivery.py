"""CLI registration for verified top-level run callback delivery."""
from __future__ import annotations

import json

from es.output import Result
from es.spec import Arg, CommandSpec, command


def _result(payload: dict) -> Result:
    return Result(0, payload, [json.dumps(payload, ensure_ascii=False, sort_keys=True)])


def delivery_verify(ctx, thread):
    from es.run_delivery import request_verification

    return _result(request_verification(ctx.cfg, ctx.agent, thread))


def delivery_confirm(ctx, challenge):
    from es.run_delivery import confirm_verification

    return _result(confirm_verification(ctx.cfg, ctx.agent, challenge))


def delivery_abandon_verification(ctx, thread):
    from es.run_delivery import abandon_verification

    return _result(abandon_verification(ctx.cfg, ctx.agent, thread))


def delivery_status(ctx):
    from es.run_delivery import status

    return _result(status(ctx.cfg, ctx.agent))


command(CommandSpec(
    "delivery_verify_run",
    ["delivery", "verify"],
    "Queue one challenge to an exact Codex thread before enabling run callbacks.",
    delivery_verify,
    [Arg("thread", "exact owning CODEX thread UUID", required=True)],
    mcp=False,
))

command(CommandSpec(
    "delivery_confirm_run",
    ["delivery", "confirm"],
    "Confirm a queued challenge from its exact CODEX_THREAD_ID.",
    delivery_confirm,
    [Arg("challenge", "one-time challenge delivered to this thread", required=True)],
    mcp=False,
))

command(CommandSpec(
    "delivery_abandon_verification_run",
    ["delivery", "abandon-verification"],
    "Retire the current verification challenge without cancelling or resending its queued message.",
    delivery_abandon_verification,
    [Arg("thread", "exact thread UUID named by the active challenge", required=True)],
    mcp=False,
))

command(CommandSpec(
    "delivery_status_run",
    ["delivery", "status"],
    "Read run callback verification and pending-event state without contacting Codex.",
    delivery_status,
    mcp=False,
))
