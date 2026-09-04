# Falsifiers

One script per conjecture node, referenced by the node's `@falsifier` tag. `es falsify <node>`
runs it as

    <script> --dataset <harness/dataset> --out <witness.json> --node <name> --statement <type>

Exit 0 = pass (no counterexample found within the search), exit 2 = counterexample (write the
witness to `--out`), anything else = error. `es falsify` records the outcome in
`harness/falsify/<node>.json` (committed: falsifier results are evidence).
Scripts starting with `_contract_` are harness test fixtures.
