# Shared immutable Lean artifacts

The project can share compiled certificate artifacts between compatible local
checkouts without sharing or symlinking a `.lake/build` directory.  Each
checkout retains the complete materialized output paths expected by Lake,
editors, and the harness.  Identical outputs are hard links to immutable blobs
in Lake's native local artifact cache.

`es storage share` discovers only generated modules in the configured
certificate layer.  It accepts these compiled facets: `.olean`,
`.olean.server`, `.olean.private`, `.ilean`, `.ir`, `.c`, and `.bc`.  It never
shares source files or mutable `.setup.json`, `.trace`, and `.hash` sidecars.
Both checkouts must use the same project id, Lean toolchain, and filesystem.
Symlinks and other non-regular output files are rejected.

The default mode is a verification-only dry run.  It reads every candidate in
both checkouts and records a full SHA-256 comparison in an fsynced JSONL
receipt.  `--apply` then asks the pinned Lake implementation to save the
canonical files with `Lake.Cache.saveArtifact`, verifies each resulting blob
again with SHA-256, and atomically replaces both local paths with hard links to
that blob.  A Lake 64-bit hash collision therefore fails closed.  Each
replacement preserves the old or new complete file across interruption; an
existing receipt can be supplied again to resume safely.

The command only runs inside `es job run`.  The native writer has a six-hour
internal deadline; the outer guarded job budget remains the governing deadline.
Python stops its complete process group and waits for disappearance before
storage leases are released on a timeout.  The default cache namespace is derived from an explicit allowlist of
supported Lean toolchains, and the command refuses an unknown toolchain rather
than mixing incompatible blobs.

Run the full operation as a guarded job because it reads hundreds of GiB:

```text
es job run --why "share verified frozen certificate artifacts" \
  --out runs/storage-share/receipt.jsonl --mem 2G -- \
  tools/es/bin/es storage share \
  --other runs/worktrees/sol-12h-20260916 \
  --receipt runs/storage-share/receipt.jsonl --apply
```

The command reserves both worktrees and the shared cache before scanning.  It
also refuses to start while an untracked Lean compiler is running.  Lake marks
cached files read-only.  On a normal rebuild, pinned Lake unlinks every old
module output before compiling, so rebuilding one checkout creates a new inode
and cannot overwrite the shared blob or the other checkout's file.

Receipts distinguish the logical bytes deduplicated from the physical blocks
that could be freed.  A replaced inode contributes eligible physical bytes only
when its pre-replacement link count was one.  The command also records free
filesystem bytes before and after the operation; this observed delta can be
noisy when other processes use the filesystem.

Do not create input-to-output cache mappings from filenames or module names.
Those mappings encode Lake's complete input trace and are produced only by
ordinary Lake builds.  A shared-cache build must set both
`LAKE_ARTIFACT_CACHE=true` and a project/toolchain-specific `LAKE_CACHE_DIR`,
and must hold the same `artifact-cache:<path>` reservation.  The package sets
`restoreAllArtifacts = true`, keeping every compiled path materialized.  Cache
enablement remains an environment choice so a bare `lake build` or editor can
continue to use ordinary local outputs without writing to a default user cache.

Lake's artifact and output-map writes do not provide a cross-process lock, so
all harness writers to one shared cache are serialized.  Cache cleanup must use
a harness maintenance command holding the cache reservation; do not run
`lake cache clean` with the shared `LAKE_CACHE_DIR`, because that command
deletes the configured cache directory.  Removing the cache directory would
not remove already linked checkout files, but it would discard the canonical
names and Lake's future-build mappings.
