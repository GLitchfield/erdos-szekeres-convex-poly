# R25 primary-source coverage

Research16, 2026-10-03 22:34 UTC. This is a record of inspected sources,
not a claim that no other manuscript exists. No source below supplies a
complete BDL proof, and no theorem credit is claimed.

- [Official SoCG entry](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SoCG.2025.13)
  links the conference version already inspected earlier. Its decomposable
  theorem proof is omitted in that version. The later journal full text was
  not obtained; its proof contents must not be inferred from the conference
  omission. Earlier publisher PDF/API failures remain recorded and were not
  repeated in this search.
- [DiGeo publication list](https://kam.mff.cuni.cz/~digeo/papers.html)
  links only that same SoCG DOI for the joint paper.
- [Jineon Baek's homepage](https://jcpaik.github.io/) rendered no manuscript
  links. Its [public website repository](https://github.com/jcpaik/jcpaik.github.io)
  lists a static site; the attempted index.html fetch returned an internal
  error and supplied no content. No hidden links were inferred.
- [Martin Balko's homepage](https://kam.mff.cuni.cz/~balko/)
  has an older publication list without this joint entry.
- [Author SAT repository](https://github.com/jcpaik/erdos-szekeres-sat)
  describes an ordered-hypergraph encoding and an upcoming draft, but its
  README supplies no manuscript link. None of its software was executed.
- [Baek's earlier manuscript, arXiv2206.04260v2](https://arxiv.org/html/2206.04260v2)
  is readable. Section3 labels edges by maximum starting-cap lengths and
  assigns each vertex a monotone vector of ending-cup lengths. It gives the
  classical grid-simplex injection. Sections4-5 specialize to two coordinates
  and interweaved laced cups for the no4-cap case. This explains a richer
  endpoint invariant, but does not prove the remaining cap>=4 ROOT obligation.
  Research search `chain slope label vector grid simplex band partition`
  returned no harness hits. The HTML sentence assigning all-one statistics
  to the rightmost vertex conflicts with its ending-cup definition; no
  argument here relies on that sentence.

Current mathematical consequence: richer endpoint/frontier information is a
possible level of abstraction, not an established induction invariant. The
classical injection alone neither assigns BDL bands nor accounts for the
strong-set budget. The exact ROOT construction remains open. Further work
must explain that connection rather than count another small boundary case.

The classical statistic also overlaps the already rejected staircase-word
compression in BDL-OBSTRUCTION.md sections32-35. Both a common window and
flexible Hall matching of short windows have retained counterexamples.
Section37 already gives exact cut-conditioned pair-rank transitions, but
their table length depends on the number of points. These sources therefore
do not justify another rank-window trial or a claim of a new general route.

## Shared repository update inspected in review36, 2026-10-04 02:02 UTC

Q25 source claude-tower-20261003/exp/q25_selfind.py was read in full,
SHA6ad107dc25c8063b97ddc67829985a92ee4992f0986d113373421560ef3d877a.
Its contract asks, for each attained Pareto parent context, for a nonempty
child threshold context whose EVERY child map extends by some classic
sibling placement. The child uses the parent's ambient band range. This
quantifier is stronger than existence of one compatible child witness.
The source chooses the first decomposable root, filters one-classic/one-wide
roots, and tests full and projected signatures. The retained
o_q25_selfind.txt (SHA2d22667327dfa7cf9d8ddc12ecc4c81a02ca27a1ccbb926bca412192f18db2e4)
reports N6/790 colorings and full-signature concatenation failures at N5.
The separately named o_q25_selfind7.txt is EMPTY (SHAe3b0c442...);
no N7 completion/coverage is inferred. None was executed or independently
replayed here. This shared diagnostic refutes taking ALL attained contexts
as a closed family; it does not refute BDL or a smaller special family.

Shared claude-lattice-20261003/NOTES.md section Q23 was read. Its final
summary leaves one/two-point anchored nearmaximum chains and cascades
unproved. PROOFS.txt provenance SHA d0112f3e3e895f210d68e52edba291a9cee9ea8268533cfd79c024852196ce22
was recorded, without importing it or claiming a new accepted theorem.
These reports agree with the regional extension-state issue in papers74/76;
neither supplies the missing mixed ROOT construction. The R25 exact
reduction, accepted inputs and receipts remain separately identified.

## Coordinator-owned root audit inspected at 2026-10-04 02:14 UTC

Job20261003-221231-81fdd3 finished rc0/24MiB. Source in the primary
checkout, runs/claude-audit-day-20261003/item7_replay.py, was read fully,
SHA5050a829266dacc97f09482640d5528d5b1581c442948c71d697c2e9a996e570.
Retained output item7_o_replay_n7.txt, SHA
30a4f26e12e4cd543c265b79a79072f2c4cff2079d9d34fea34079136abfbb03,
reports1262406 checked parent partitions and FAILS[] through n7. The
audit covers the conditional BRL+=>BDL root constructions, including all
valid ordinary child supplies and positioned BRL witnesses, plus literal
duality. Its consecutive-chain DP uses the generated decomposable input's
one-change property; strong recursion checks middle determinacy. Default
MAXPAIRS1e9 is inactive here (even all child assignments<=6^6). It checks
BRL's premise by finite search, not a general theorem, and does not replay
paper81's n15 case. This is separately owned shared diagnostic evidence,
not an R25 job, delegation, proof receipt or new independent execution here.

## Full-core BRL24 witness — independently replayed at02:34UTC

Shared node journal artifacta47922b73ab8d2f759fb09035da6248dfef360f75db95e7255a1facddedb0d53
reported the exact tag g657n25d1-32, mirror0, originalpoint7 deleted,
from primary runs/claude-tower-20261003/i_wide4.pkl. The report was not
initially taken as an own result. Immutable local dataset snapshot SHA
4365fb72752c27cf137631d1105aeefd3ffc365a30b459b4e2a48c99ecec4a80
and exact copied checker sources were read before guarded execution.
Shared zl.py SHAeca6b43f... and ex_hard.py SHA6b5b167f... were read for
semantics: SAT clause sizes/index bounds agree with the stated BRL+.
At02:26 its o_hard.txt was still partial/running, so no complete scan
coverage was inferred. The explicit witness came from the separately
reported check, not a completed broad scan.

Own brl24_recheck.py SHA6d23f4d20bf69a8033d0176affc4bc6508488d6f17107598ec9d32660865a7f9
and dec_audit.py SHA4031e8f3fdaefe4316a6c259f82c0061694b56977b6ff86743ed130bcfabfb52
are byte-identical copies of the independent audit checker. Resource-only
pilot223237-f65078 pins every label in brl24-resource-pilot.json,
SHA580a2c04bb629ff0bb299e5d5340d4e570ee272d165e49ea09f2021477747b7b.
Own exact replay223307-714ff0 passed10.6s/1613MiB: n24,c4/d5/sigma6,
core(6,15), both inclusive one-sided bottom queries false. Gap7 singleton
ordinary partition exists with z inband2. Result SHA
723c2121c08c176673209dc52e64d6dd148649f7a87b7f0578ae70f2a3c02be3.
This independently supports the diagnostic BRL+ refutation (paper82),
not a Lean certificate or counterexample to BDL/ordinary MIXED ROOT.
No other gaps or sibling-specific bottom-only query were executed here.

The Q25 empty-output statement above is historical as of02:02, not a
permanent absence claim. A later shared node journal reports completed
n7 sampling and universal-context failures; not independently replayed
here. The mathematical consequence, all attained threshold contexts are
not automatically closed, is unchanged. A special context family remains
open and is not supplied by either finite report.

## Late shared journal — read02:44UTC, no new independent replay

Artifact3968c872918f117aef2df3715b301866105139eef810000bccb5015b4a44b8ae
contains the late coordinator synthesis. Its guarded conditional
BDL=>Theorem8 scratch reportedly compiles (job222711-a295f2) after fixing
an all-j band condition: j=k excluded0-caps and made the original premise
refutable, so the corrected hypothesis guards j<k. This is a conditional
reduction owned elsewhere, not BDL, and no source/import/receipt is
accepted as new R25 Lean work from the journal alone.

Hard ZLOCK scan221957-182fd0 is now reported complete. The earlier
partial-output observation above remains accurate as of02:26, not a
permanent coverage claim. The report agrees with our exact n24 gap7
ordinary partition and stronger BRL+ failure; other gaps/sets remain
shared-only evidence here.

The latest Task2 account (223951-1044bd,223851-ea4b66) rejects treating
multi-point case R as repeated singleton ZLOCK: after the first A point,
a later point is not a lower singleton of B plus prior A, since a triple
with the prior A in its middle changes color under that proposed split.
Its joint keep/lift condition requires kept cup-interval avoidance and
lifted cap prefix/suffix AND two-endpoint interval bounds. This agrees
with our explicit paper76 regional equations. Reported finite keep-all
successes neither prove universal normalization nor close MIXED ROOT.
These new source files and broad outputs were not independently read or
executed here; only their journal account was inspected. No owned jobs,
Lean theorem credit or new trial are inferred.
