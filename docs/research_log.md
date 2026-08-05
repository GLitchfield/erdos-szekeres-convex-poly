# Research log

Index designed computational experiments here. Environment smoke checks and
routine reproductions are infrastructure checks rather than numbered
experiments.

| Test | Question | Evidence level | Status | Artifacts |
| --- | --- | --- | --- | --- |
| 0021 | What do two probes with bridge certificates on one frame force? | Exhaustive `2^10` five-vertex audit; positive survivor proved in Lean | Complete | [Note](experiments/0021-middle-bridge-certificates.md), [analyzer](../scripts/analyze_two_probe_bridge_compatibility.py) |
| 0022 | Can local middle-pair bridge data force a shared frame or extreme replacement? | Four independently replayed SAT models; no Lean promotion | Refuted computationally | [Note](experiments/0022-middle-bridge-route-counterexample.md), [generator](../scripts/check_middle_split_bridge_routes.py), [checker](../scripts/verify_middle_split_bridge_route_model.py) |
| 0023 | Can global packing or realizability repair the local middle-split route? | Packing censuses and LRAT dependency audit; rational realization promoted to Lean | Both modest repairs retired | [Note](experiments/0023-packing-and-realizability-route-gates.md), [Lean realization](../ErdosSzekeres/StructuralChargingMiddleSplitRealization.lean) |
| 0024 | What is the exact one-step singleton residual of the open anchored profile at `k = 6`? | All 186,888 children and 18 contexts, independently replayed | Oracle complete; rooted-footprint compression pending | [Note](experiments/0024-singleton-residual-oracle.md), [producer](../scripts/enumerate_singleton_residuals.py), [checker](../scripts/check_singleton_residuals.py) |
| 0025 | Does exact endpoint-span rank retain enough correlation for singleton observation and transition? | All 186,888 children and 3,363,984 singleton extensions, independently replayed; side-labelled cut semantics proved in Lean | Singleton gate passed; interleaved follow-up completed in 0026 | [Note](experiments/0025-span-rank-footprint-gate.md), [Lean](../ErdosSzekeres/RootedChainFootprint.lean), [manifest](../data/derived/e3-span-rank-footprint-k6-n9.json), [checker](../scripts/check_span_rank_footprints.py) |
| 0026 | Does the endpoint-span footprint remain congruent under the smallest feasible two-vertex interleaved roots? | Uniform singleton transition bundle proved in Lean; 762,912 two-root parents independently replayed | Interleaved-root gate passed; ambient-free dominance quotient pending | [Note](experiments/0026-two-root-span-footprint-gate.md), [Lean](../ErdosSzekeres/RootedChainFootprint.lean), [manifest](../data/derived/e3-two-root-span-k6-n9.json), [checker](../scripts/check_two_root_span_footprints.py) |
