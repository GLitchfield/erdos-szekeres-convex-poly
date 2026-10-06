# General endpoint lifting — accepted

2026-10-03 23:46 UTC. `ErdosSzekeres.ctx_part_endpoint_path_lifting` is
CLOSED, unchanged locked type `5f51f6e3b493f420`, with no sorry and only
`propext`, `Classical.choice`, `Quot.sound`. Supported node-finish operation
`op-58b7ff64fee64da9` succeeded in all five stages. One-node local commit
`fa6dacd1d830e63512a3a83f6e7387a00f26ccc6`, job `20261003-194500-5a2fb6`,
contains exactly the module, root import, nodes, lock and status files;
`left_uncommitted=[]`. Automatic claim release is CLOSED, as verified in
the actual full journal. No merge, push or publication.

For any raw context, part, side and sibling maximum, explicitly assume the
new level has the chosen side. Select zero or one level-one marker strictly
before the child's start, and zero or one strictly after its end. With total
gain g, both the old pure extension and old join extension at the selected
endpoints increase by at least g in the part. The new maximum m is also a
join candidate. Every positive chain size r below the child's growing-color
limit therefore satisfies r+g below the parent's corresponding endpoint
limit and r+m<=k-1. No wellformedness, coloring, occupancy, positive maximum
or ordering-of-start/end hypothesis was added.

The proof selects new markers before mapping an old attaining extension
path through shifted levels. Position monotonicity compares the selected
marker with the greedy first step; the fold count offset supplies one gain.
The two ends add independently. Shifted old maxima account for every old
join candidate. Positive r excludes saturation of natural subtraction at
zero, which is essential for the limit and coupling conclusions.

## Exact evidence

Searches: `part-endpoint-path-lifting-search.json` and
`part-endpoint-limit-consumer-search.json`. Registration
`20261003-190710-3ee182` and capture `20261003-190952-5a5854` passed.

Fixture:
`167421e2fb29d6b26b68c5efee4a7e6f883fa3ea502f726130f5600b4b0bbdc1`.
Body v3:
`cdf14855f288c4c998c3144ad6fef8f7de510c5265ab7a1b7b998c1da8cbbc71`.
Original source:
`e6ca6060cad4b5c7890cc1b387ba05f82857f1a12da4907e7a6d99d83a1f409c`.

Isolated v3 `op-08dd8d703bb742c0`, job `20261003-191451-b84563`, passed
15.826406 seconds / 2102 MiB, standard axioms. Receipt:
`c5192f26463149fd7f8b9c186ebff7d7a3757862f462bcf1a6777ff7689e1077`.

Normal finalization receipts:

| stage | job | result | immutable receipt |
|---|---|---|---|
| candidate |20261003-191531-eff7d9|13.5457 s / 2101 MiB, accepted|40d998f92f0df4f2f3f97674dd17a404820168d4223cf00b91afded794fab14a|
| original source |20261003-191550-a7a040|66.5806 s / 2361 MiB, unchanged type, no sorry, standard axioms|da0cfa77fb3e42df74c8ebd079ac7d11db7379a84ebfd9a7f6b944f782546e78|
| full extraction |20261003-191701-14ca1a|1578.862611 s / 5656 MiB, fresh frontier, problems=[]|7f1d7d51b12d4d3e93a48cc8f69c3a3c5e7d65ef21e500e6b72663dfdd0b7d45|
| audits/layers |20261003-194326-0a2da4|12.8651 s / 100 MiB, failures=[] / violations=[]|e7e3230a91440246a8816a8ba5d975b1040a7619adb5cb645419e32c4f3ca8ef|
| review preparation |20261003-194343-24d23e|0.2210 s / 11 MiB, accepted, published=false|fa16487daa90ad2f1f197d67cfcf0d164b744931c199e0e2f2139ad29bcdb23b|

`part-endpoint-node-finish-final.json` contains the complete operation.
Full status has `stale=[]`, `problems=[]`; final node status confirms the
locked type, no sorry and standard axioms. Full extraction processed
15,834 modules and retained 12,910 index declarations. Its actual complete
result, rather than the earlier scan counter, grants full validation.

The entire source, statement and immutable 11,774-byte review diff were
read against the accepted body/source hashes. Diff
`d7a72ffdffa7c3aade942e3a503bd85b171f1c16bb320cefbc956df8977acb07`
was fetched with limit 20,000 and `next_offset=None`; `--full` alone still
paginates text. The statement is unchanged, and `git diff --check` passes.

Failed v2 `op-c77075d9d09b42a1`, job `20261003-191350-92af89`, took
11.9134 seconds / 439 MiB. Its two errors were parentheses around max?.getD
and final dependent-match assembly. Receipt
`6121d58a41e2665a74dd52f01ff0fec990c3cf8b317c2f641a76453d7e9223ab`
and all body versions/diagnostics remain preserved. No hypothesis narrowing.
Checkpoint reviews left the full job running on its measured prior scale.

## Remaining mathematical obligation

This theorem does not prove B attainment, matrix equivalence or a maximum.
Updated 2026-10-04 01:21 UTC: the semantic assigned-limit transfer is fully
accepted `e0e31525`, unchanged type `a89e497ebd1cfbea`, including positive
and empty mixed cores. `ASSIGNED-LIMIT-TRANSFER-ACCEPTED.md` gives its full
evidence. Joint placement and induction over the actual finite recurrence
remain separate general obligations.

The universal T lower theorem is fully accepted `aebb6505`; its
Pascal/window invariant retains decomposition. The one-zone upper
N<=T and a closed endpoint-loss invariant remain open. Wellformed positive
external IDs are explicit in the hand matrix/B construction; the raw
endpoint theorem itself uses only its stated side premise. No finite-instance
Lean target or numerical theorem credit was added by this closure.
