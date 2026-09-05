# es — blueprint harness

Project state (what is proved, open, claimed, and what depends on what) is derived
from the compiled Lean environment. Design: `docs/harness-design.md`; what deviates
and why: `docs/harness-implementation-2026-09-04.md`.

    tools/es/bin/es doctor            # toolchain, config, database, oleans, cache
    tools/es/bin/es status | ready    # the frontier / claimable nodes
    tools/es/bin/es node add ...      # new statement (elaborated, deduplicated, locked)
    tools/es/bin/es check <node>      # build the node module, re-extract, report sorry/axioms
    tools/es/bin/es build core        # memory-guarded, budgeted lake build
    tools/es/bin/es layers | audit    # import layering / axiom allowlist checks
    tools/es/bin/es lock refresh --all --reason "toolchain vX"   # re-approve unchanged statements after a toolchain bump

Install for development: `uv venv tools/es/.venv && uv pip install -e "tools/es[test,mcp]"`,
then `pytest tools/es/tests`. The MCP server (`tools/es/bin/es-mcp`) is registered in
`.mcp.json`; the Claude Code hooks in `.claude/settings.json`; the nightly check in
`tools/es/systemd/` (`install.sh` enables a user timer at 03:00).

## Things that cost hours to learn

- **Never `import` the project modules at the top of a `lake env lean --run` script
  that also calls `importModules` on them.** The script's own import maps the oleans;
  the second load cannot mmap at the same addresses and reads them into anonymous
  memory instead: 37 GB and a cgroup OOM kill for the certificate closures. The
  extractor template imports only `Lean`; `main` imports the project.
- **Never use `importAll := true`** for the extractor environment (30+ GB). A plain
  import exposes every theorem value in `env.header.moduleData`.
- **Never run bare `lake build` on big targets.** Lake 5 has no `-j`; 22 parallel
  compilers exhaust the 20 GB guard. `es build` builds Lake's out-of-date list one
  module per guarded invocation first.
- **`#print axioms` does not finish on the certificate families** (16 TB read in
  3.5 h on 2026-09-04); the extractor's module-order taint scan with the per-module
  cache in `~/.es/<id>/taint/` is the audit path. Its first scan of a family takes
  tens of minutes; afterwards an extraction is about a minute.
- **Hand-written modules in the import closure of a certificate family are frozen**
  (`harness/encodings.txt` pins the direct inputs; `es layers` fails on a diff to the
  closure unless the commit message carries `[certificate-rebuild]`).
