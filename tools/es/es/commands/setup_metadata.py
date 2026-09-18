from __future__ import annotations

import os
import time
from pathlib import Path

from es import EXIT_OK
from es.build import lean_compilers_running
from es.context import Ctx
from es.errors import CheckFailed
from es.jobs import check_outputs
from es.output import Result
from es.setup_metadata import prune_setup_metadata
from es.spec import Arg, CommandSpec, command
from es.storage import exclusive_storage_maintenance


def run_prune(ctx: Ctx, apply: bool = False, out: str | None = None) -> Result:
    """Inventory or remove pinned Lake setup metadata under an exclusive worktree lease."""
    relative = out or f"runs/setup-metadata/{time.strftime('%Y%m%d-%H%M%S')}"
    normalized = check_outputs(ctx.cfg, [relative])[0]
    output_dir = ctx.cfg.root / normalized
    owner_job_id = os.environ.get("ES_JOB_ID") if os.environ.get("ES_IN_GUARDED_STAGE") == "1" else None
    with exclusive_storage_maintenance(
        ctx.cfg,
        [ctx.cfg.root],
        reason="Lake setup metadata pruning",
        owner_job_id=owner_job_id,
    ):
        running = lean_compilers_running()
        if running:
            raise CheckFailed(f"refusing setup metadata cleanup while {running} Lean compiler(s) are running")
        receipt = prune_setup_metadata(ctx.cfg, apply=apply, output_dir=output_dir)
    summary = (
        f"{receipt['status']}: {receipt['files']} file(s), "
        f"{receipt['logical_bytes']} logical bytes, "
        f"{receipt['allocated_bytes_reclaimable']} allocated bytes reclaimable"
    )
    if apply:
        summary += f"; reclaimed {receipt['allocated_bytes_reclaimed']} allocated bytes"
    return Result(
        EXIT_OK,
        {
            "status": receipt["status"],
            "files": receipt["files"],
            "logical_bytes": receipt["logical_bytes"],
            "allocated_bytes_reclaimable": receipt["allocated_bytes_reclaimable"],
            "allocated_bytes_reclaimed": receipt["allocated_bytes_reclaimed"],
            "manifest": receipt["manifest"],
            "receipt": receipt["receipt"],
        },
        [summary, f"manifest {receipt['manifest']}", f"receipt {receipt['receipt']}"],
    )


command(CommandSpec(
    name="storage_prune_setup",
    cli=["storage", "prune-setup"],
    help="Audit or remove Lake 4.29.1 *.setup.json files under an exclusive storage reservation.",
    run=run_prune,
    args=[
        Arg("apply", "unlink exactly the files captured and revalidated by the manifest", "bool"),
        Arg("out", "artifact directory under runs/ or data/"),
    ],
))
