# R18 raw single-run normalization proof review

Exact registered type30723e3b90f91c84, unchanged after proof repair. Arbitrary raw
globals,k,m and one indexed maximum; uniform child/ext1side word, numRuns<=1.
The normalized word retains both endpoint-presence flags and the indexed [m].

Empty support gives bound0 on both words. Otherwise checked interval reasoning
fills a contiguous child span. A level1 marker left/right of the first child
exists exactly when the respective endpoint flag holds. This gives identical
one-level left/right extension counts, sideAt (including defaultlower when no
physical marker), joins, capacities, and the single-run base. No legal-parameter
or well-formedness assumptions were added to avoid raw edge cases.

Isolated acceptance134427-e4b930/op-3fbcb2cce62c4d4d,10.02s2105MiB;
fixture5d6abf43e7124f8995852621942b5794eebbd62384fd529521ffcb1230aed0f0,
body79e1b7a3f04a98917b0ac96fe43ec1aefa04921a9d174aee9c4223c1a0ea4542,
candidate9ae4436a95cdf36d52b653461daee9009ca4d62252435f55ea2bc2cd96639b08,
receipt53177f7f7c8872785057cb96ad9a944b0e65068d8dcc3ba402bc530c91c43e47.
Audit only propext,Quot.sound,Classical.choice. No open NF dependency.
Original-source targeted check134527-879206 CLOSED at17:51Z,7.26s642MiB;
sorry=false,lock_ok=true,exacttype and standard axioms only. Final receipt
37aa6a229f6a6446c562fefb90e4ffec6b2b79821e1ff17c15d655d94df14d9c.

Failures v1..v4 are preserved separately. They concern tactic indentation,
self-referential rewriting, an opaque local marker contradiction, helper APIs
outside the imported core, and premature filter-to-find simplification.
The final proof uses only core definitions and preserves the exact statement.
This removes the single-run NF obligation; paired multirun transport and the
reverse comparison remain open. It supplies no full ROOT-NF/C1r theorem credit.

Search before statement/proof is recorded in SINGLE-RUN-NF.REQUEST.md and the
harness journal. The hInterval proof reuses the checked contiguity argument in
CtxBoundMonoOfZeroCapacityMarkerInclusion; no duplicate public lemma was added.
Strict inherited lock repair restored19 metadata entries with every inherited
type_hash/type_pp unchanged; LOCK-REPAIR.single-run-nf.json is the provenance.
The temporary local registration cap was restored before capture/check.
