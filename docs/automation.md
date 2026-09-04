> **Harness note (2026-09-04).** Trust policy is now enforced by `es audit`: every
> non-standard axiom reachable from a blueprint node or a destination theorem must be
> covered by an entry in `harness/allowlist.json` (`reaches` names the theorems it may
> reach). `sorry` is allowed only under `ESBlueprint/`. Generated certificate modules
> form the `ESCertificates` layer (patterns in `harness/config.toml`); `es layers`
> checks the import boundary. Builds run through `es build` (cgroup memory guard,
> wall-clock budget). See `docs/harness-design.md` §7.4 and §10.

# Lean automation policy

The project uses automation to discover and check local proof steps. Automation
does not relax the completion standard: every accepted theorem must elaborate
to a proof checked by Lean, without `sorry`, `admit`, unsafe axioms, or an
unverified external oracle.

## Adopted stack

- LeanHammer `v4.29.0` at commit
  `6ea795e19edb540a55e16dd4fed1a263324909b8`, Apache-2.0, retrieved 2026-08-02 from
  <https://github.com/JOSHCLUNE/LeanHammer>. It is listed before mathlib in the
  Lake manifest so Lake favors mathlib's shared dependency versions. A local
  compatibility build established that this release compiles with the
  project's Lean and mathlib `v4.29.1` pins. `lake-manifest.json` records the
  exact resolved commits locally. The direct Lake dependency is commit-pinned;
  Hammer's committed manifest pins its transitive dependencies.
- Hammer brings the Apache-2.0 Duper and lean-auto proof-search components.
  Zipperposition is downloaded by lean-auto's Lake hook. Because `unzip` is not
  installed on every development host, `make update` prepends the repository's
  minimal Python compatibility command in `scripts/toolchain/` to `PATH`.
- Aesop and Grind remain the first choices for small structural and local
  semantic obligations. Project-specific safe rules may be registered only
  when their search behavior is predictable and the resulting build remains
  bounded.
- Large finite claims continue to use committed LRAT certificates checked by
  `Mathlib.Tactic.Sat.FromLRAT`. `bv_decide` may be used for exploration, but a
  central result should use the existing raw LRAT path unless the trusted-base
  policy is explicitly changed.

## Working modes

Use ordinary Hammer interactively:

```lean
by
  hammer
```

Hammer prints a smaller replacement tactic. Prefer committing that explicit
script when it is stable. For a reproducible call that does not contact the
public premise server, disable selected premises:

```lean
by
  hammer {aesopPremises := 0, autoPremises := 0}
```

`ErdosSzekeres.Automation.hammerOfflineSmoke` build-gates this offline mode.
External ATP success counts only when Hammer reconstructs a Lean proof. Raw
solver output, model agreement, or an unverified SAT result is evidence rather
than a completed theorem.

## Search and agent tools

Loogle, LeanSearch, and LeanExplore are useful for finding declarations but do
not prove the selected result. Lean LSP integrations may expose goals,
diagnostics, and search to an agent; their output remains subject to `lake
build`. Neural proof systems may propose tactics, but generated proofs receive
exactly the same kernel and no-axiom checks as handwritten proofs.

The validated agent setup uses the MIT-licensed
[`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp) `0.29.0`, pinned in
the Codex MCP configuration, together with the MIT-licensed
[`lean4` theorem-proving skill](https://github.com/cameronfreer/lean4-skills).
Both were retrieved 2026-08-02. MCP and skill inventories are loaded when an
agent session starts, so a new session is required after first installation.
