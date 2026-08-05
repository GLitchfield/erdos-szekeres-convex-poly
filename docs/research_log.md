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
