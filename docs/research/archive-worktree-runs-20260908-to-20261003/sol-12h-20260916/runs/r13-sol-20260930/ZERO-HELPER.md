# Zero global-axis helper

Node `ctx_bound_zero_of_unit_global_axis`, hash`3f2964484062c828`.
For every raw context sigma with a<=1 or u<=1, every boundFuel and bound
vanishes. No well-formedness, positivity, indexed-level or k hypotheses.
This covers C1r's a/u=1 parameters, where the existing expansion theorem's
WellFormed premise is unavailable.

Proof: zero cap or cup gives base0. Parts keep the same global parameters.
Induction on fuel sends every cut sum to0; the list maximum is0. The proof
was already compiling inCore.lean/job20260930-162839-1e7956, then generalized
to expose all fuel approximations as well as full bound.

Search before writing: `search-zero-global.json` had no registered match;
registration20260930-174521-a8e0b3 also checked complete-index duplicates.
Closest results bound by a point-base sum or number of runs, rather than
this raw zero-global-axis equality.

Captured fixture23530e6e40512a8581d52afea64695035cd989f6e441a990b083097be95d09d5,
proof checkop-240299ed72764811/job20260930-174832-d8e6f8 accepted the complete
parent with standard axioms only. Exact accepted source hash
d9910f9a6ea013f30c7f9f4cc6f7ba68e9bda1e4bf654059c041fd4eed6ac957 installed
unchanged. Targeted module check20260930-175052-dd087d completed rc0.
`NODE.zero.json` and`RECEIPT.zero-targeted-check.json` record the audited result;
actual proof receipt at runs/es-operations/20260930-174832-d8e6f8/receipt.json.

The first targeted-check submission used an unsupported --mem flag and
failed before any job; logged and corrected to the supported guarded default.
No theorem credit was inferred from that failed command. No new algorithm
or workflow helper was written; candidate body reuses the Core fuel proof.

This closes only a reusable boundary branch. Multi-run C1r upper domination
and the singleton reduction needed to derive it from X remain open.

Committeddd4291f419eef48178c2c75d9e839b6de18defa3 on
node/CtxBoundZeroOfUnitGlobalAxis,job20260930-175305-aa3cbc.
Targeted full audit NODE.zero.full.json confirms closed,sorry=false,
standard axioms only and lock_ok=true. Claim released closed.
