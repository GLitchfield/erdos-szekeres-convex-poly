# Integration of R19 + R20 (prepared 2026-10-02 ~15:10; MERGE NEEDS GAVIN'S APPROVAL)

**Worktree.** `runs/worktrees/integration-r20-20261002`, branch `integration/r19-r20-20261002`, from main `6e4d0e66`.

**Done so far:**
- `d6d816d7`: cherry-pick of R20 `c89df0e8` (`diagonalCupBlocksForce4kk_of_five_le`). Clean.
- `b8815083`: cherry-pick of R20 `82a57072` (`singletonLowerPascalTailGate_four_diagonal_of_five_le`). Merges:
  - ESBlueprint imports: union.
  - statements.lock: the gate record inserted textually; both sides only add records, and all 435 base records are
    unchanged.
  - nodes.json / index.json / status.md: kept from HEAD, for the full extract.

**Remaining (after R19's terminal review at ~20:30):**
1. Cherry-pick R19's accepted commits. They are based on `e3c87197`, i.e. before the R16–R18 integration. Reuse
   `runs/claude-integration-20261002/integrate.py` logic (structured lock and import merges).
   - split_attained `991b7839`, split_le `e2902639`, flank_swap `e05ed9a3`;
   - the PEEL registration `528caa7e` (refuted statement) and its refutation `119a082b`;
   - `ctx_satisfies_pair_limits`, plus any later items listed in R19's handoff.
2. Full `es extract` as an es job (28G guard), then `es audit` and the es tests.
3. Ask Gavin; on approval, fast-forward main and push.
4. Optional cleanup: replace the gate module's duplicated proof body with a call to the uniform theorem. This edits
   no statement, but needs a re-check.
