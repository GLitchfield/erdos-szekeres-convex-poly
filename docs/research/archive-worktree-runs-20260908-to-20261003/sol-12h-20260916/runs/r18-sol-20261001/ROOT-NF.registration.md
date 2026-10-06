# ROOT-NF registration (R18)

The new conjecture `ctx_one_level_root_bound_normal_form` replaces a one-level root
word by one child per run, preserves the presence of each end marker, and clamps
the run count at three when either global axis is two, and at two otherwise.
It retains the original maxima `[m]`, including when the old marker is absent.
The signature covers all legal globals `1 <= a,u <= k`, `3 <= k`, `1 <= m <= k-2`.

Branch `node/CtxOneLevelRootBoundNormalForm` starts from local main
`b231fee6ae19ad8623809d48131cdb535234ab01`. No existing statement changes.
The conjecture has a proof hole and establishes no theorem yet.

`es search` for one-level root normal form and for a normal-form implication of
child contraction found no matching declaration. The closed
`ctx_num_runs_child_letter_contraction` (type `87d38cf7fc07a108`) supplies the
run-count invariant for a separate conditional C1r-from-NF node.

Targeted registration: job `20261001-113638-c3a27f`, terminal rc0, locked type
`e0cedb9ee88cc591`; exact receipt `register-root-nf/DONE.STATUS.json`.
Targeted falsifier: job `20261001-114749-eba325`, terminal rc0/pass, 29,520 cases,
zero violations. Exact record is
`harness/falsify/ErdosSzekeres.ctx_one_level_root_bound_normal_form.json` and
`falsify-root-nf.DONE.STATUS.json`. Cases: k=3,4, one to four children, both sides,
all legal globals/maxima, end multiplicities 0,1,2 and separator multiplicities
1,2. Compiled evaluator semantics are `context-bound-zero-children-c-v1`;
these tests give diagnostic evidence without C-to-Lean proof equivalence.
Zero-child words are allowed by the Lean statement but excluded by the evaluator.

Targeted check `20261001-115504-d79ec9` finished DONE rc0. Its immutable detail
`bc5b52889c7c0b1d4b4cb67623c79283814324d90cec0935af7adcf0e863417b`
is copied to `check-root-nf.DONE.RECEIPT.json`: targeted=true, lock_ok=true,
type `e0cedb9ee88cc591`, sorry=true, standard axioms plus the expected sorryAx.
The root module build took 2.76s and peaked at169MiB; the subsequent targeted
metadata operation was longer. This is registration evidence, not a proof.

The inherited main `harness/statements.lock` was malformed. Nineteen metadata
records were restored from their exact original R15 commits, with all inherited
`type_hash` and `type_pp` fields asserted unchanged. `LOCK-REPAIR.json` and
`repair_inherited_lock.py` retain the provenance. This metadata repair accompanies
the new entry; it introduces no statement changes. The full index remains stale
because an unrelated 28.5GiB module exceeds the 4GiB targeted closure ceiling.
No full extract was run. A temporary tighter 8G local build cap enabled guarded
registration and was restored to the original config before this checkpoint.

Part2 transport probes and their failures are documented in
`MATHEMATICAL-HANDOFF.md`. ROOT-NF itself remains open.
