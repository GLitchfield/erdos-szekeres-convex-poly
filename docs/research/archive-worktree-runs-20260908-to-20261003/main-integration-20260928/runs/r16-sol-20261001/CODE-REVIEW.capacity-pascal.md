# R16 capacity-Pascal review — 2026-10-01 07:30Z

Configured gpt-6.1-sol/xhigh self-review in window-d3db95196e9841c3.
No other model or delegation authorized, so no separate Astra reviewer.

Exact theorem:3<=a<=k,2<=u<=k implies
T(a,u,k)=T(a-1,u,k)+T(a,min(u-1,k-a+2),k).
Statement preserved from es node add; no existing statements edited.

Accepted targeted check20261001-032731-9e217b:
typehash909643c533edfebe,lock_ok=true,sorry=false,only standard axioms.
CHECK.capacity-pascal-v1.json SHA256
c2991a671fd53891d303c8bf2796ab1c3c57d6c05605667d92881874ffb73e68.
Closed fixturea6f75b1f619b42dd918a5d78e21164751440b806e1ac555fa642921abbe9c442.
Module source SHA256474a0488b2e5bef06fffc14646abb8153e5d38f03388d65e7b41aae4a8e68ae4.
Build3.420874357s,enclosing20Gjobpeak2339MiB. Incremental,targeted,no full extract.

Proof review:
- Finset Icc splits exactly into its lower endpoint and the remaining interval;
  disjointness and endpoint membership proved by natural arithmetic.
- Transition x+y=k+3: choose expression is exactly two adjacent entries of row
  k-2, using choose symmetry and Pascal. Explicit legality prevents truncated
  natural-subtraction artifacts.
- u2: capped u1 termzero; remaining termsboth1.
- Inactive regime: cap=min(u-1,k-a+2)=u-1 and ordinary Pascal applies.
- Active regime: cap=k-a+2 and second term is the lowest window entry.
  First term uses window except at transition, handled by the exact local helper.
  The complete lower-end window split proves the sum, including a=k.

No axioms,native_decide,sorries,certificate edits,or conditional open premises.
No claim of N_ends closure: arithmetic identity still needs point-potential,
singleton-form and context-normalization consumers.

Ad hoc-code review since prior review:
- Pascal proof and immutable signature/body snapshots only.
- Point-base runner/candidate unchanged since reviewed v2; source hashes match
  prior snapshots. K6 timing one0.026966659s/41MiB,both0.023094879s/39MiB,
  one fixture each,no violations. These are diagnostics,not receipts.
- Inline commands are guarded es check/job submissions and readonly repository
  inspection; branch-local N_ends-tagged submissions rejected before job creation,
  then logged/reissued under existing N_root.
- No new workflow/Python glue. Shared C evaluator,root generator,and threshold
  implementation reused unchanged. No algorithm promotion needed for this
  one-off mathematics. Useful theorem is a registered ESBlueprint node.
- Node commit will include only module,root import,lock/index records.
  Preserve ignored run artifacts independently; no integration/push.
