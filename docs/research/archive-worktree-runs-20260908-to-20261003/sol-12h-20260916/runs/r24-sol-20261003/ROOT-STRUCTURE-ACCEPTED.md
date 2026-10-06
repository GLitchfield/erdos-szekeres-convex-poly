# Accepted general root structure

2026-10-03 18:11 UTC. `ErdosSzekeres.two_full_cap_blocks_root_structure` is
CLOSED with locked type `84e6237f7f3a6146`, no sorry and only `propext`,
`Classical.choice`, `Quot.sound`. Final operation `op-130d007913064c93`
succeeded under review policy; it made no publication or remote change.

Commit `13b050e1a9259605e864a30c7f1516699c5be18e` on
`node/TwoFullCapBlocksRootStructure`, guarded commit job
`20261003-141241-efeb07`, contains exactly the node module, root import and
three harness records. No files remain uncommitted; post-commit status is
fresh with no problems. Prior research/R18/R19 refs are preserved.

For every p>=4, let a nonempty deep-below root split the union of two disjoint
full p-cap sets, avoiding both a(p+1)-cap and a(p+1)-strong set. The lower
child has exactly two points in each cap set, is itself a four-cap, and the
upper child has2p-4 points with cap rank exactlyp-2. Neither order separation
of the cap sets nor sweep realizability is assumed.

The key mechanism is root coupling. A full upper cap block with any lower
point already forcesp+1 strong. If upper misses one block, lower contains a
p-cap and an extra point; global cap avoidance forces a three-cup, which
couples with at leastp-2 upper cap points to forcep+1 strong. Thus both blocks
meet both children. Existing cap intersection geometry bounds each lower
contribution by2. A lower two-cup forces the upper cap contributions at most
p-2, giving equality2+2. A lower three-cup or an upper(p-1)-cap would again
violate the same root coupling, proving the remaining chain conclusions.

Receipts:

- Fixture `528a87199365bf233ebe5249b1a0a6f9cfdc45157c157f54ed42216b106eab79`.
- Accepted isolated v2 job `20261003-134701-7e1d3c`, receipt
  `d1b02ae6c07291c7d0997408ea5a2093f03716be0701b59c24ff7c7a0b1135e6`.
- Final candidate `20261003-134830-14a5f0`, original-source check
  `20261003-134841-d86a75` (receipt
  `911f33c8cd9f4b1cd506e274358303446446d29864a682afd92fe89c74216edf`).
- Full extraction `20261003-134932-d2c521`,1167.474s/6556MiB, receipt
  `7efa04c8e72221989aced2072057514ec537ad06cac100ca0bdb691a20a81798`,
  fresh frontier, no problems, tree `25835ac5b63a1d1b.4560d6f33c43b8ee`.
- Audits `20261003-140905-95e9f2`: no axiom audit failures or layer violations.
- Review `20261003-140924-7dd454`, receipt
  `0246c05342a66e779a43300ec765d1a3db0ec1e5d400596593b48b65855a8c95`;
  proof diff `ade440a89d1fccde308b0051175b2d035694af081d48d77de255d912bdf7cf7f`.
- Source SHA256 `6ef0aff141406c1d98dc45be41248951bdac72b5493afa6b5698a5723f2794d7`.

`root-structure-final-operation.json` preserves the complete operation. The
proof is `root-structure-proof-v2.txt`. V1 and its failed receipt are retained:
the only error was a redundant tactic after all goals were solved. No change
to the registered statement or trust basis was needed.

The next reusable consequence is the endpoint/four-cup/noninterval theorem in
`ROOT-ENDPOINT-PROOF-PLAN.md`. General constructions, B attainment and matrix
state equivalence remain hand/diagnostic. The accepted root theorem does not
certify the entire literal10/9 counterexample or a closed general N formula.
