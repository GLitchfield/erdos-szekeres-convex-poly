# Kernel-certified k4 end-only exchange obstruction

Node ctx_k_four_end_only_maximal_segment_flip_counterexample on branch
node/CtxKFourEndOnlyMaximalSegmentFlipCounterexample. Type2be8fbabfb76989f.
Commit ef73bf0200e3f05417c33dc89450b85f5ed3c2b8, guarded commit
20261001-050700-b7fbb3 done0. Claim can be released closed.

Exact witness: a4/u3/k4, word S,1L,S,S,S,1L,S, maxima1. WF, at least2runs,
child positions0,2,3,4,6. Keep0,3,6 and rest2,4 are both noninterval.
Old upper1/ lower2 partition sum is2. First flip removes child0 and last
flip removes child6 from keep. For either resulting partition, both
orientation sums are<=1 for every legal d (1 or2). Thus no endpoint
maximal-segment flip can dominate the old value. This certifies an exact
obstruction to end-only exchange, not a counterexample to full FLIP.
Interior maxima2 remain finite C evidence, not asserted by this Lean node.

Accepted targeted check20261001-050411-133fb3:134.1s outer/7922MiB/OOM0,
build98.42537498474121s. Full5212B receipt
0ae83452b983b9f0e68b17253556a6144b57f9c6b6f288b7072827cc9520ced9,
CHECK.k4-end-counter-v1.full.json. Closed/noSorry/Std/locktrue/blocks[]/
errors[]/targeted+incrementaltrue. Capture fixture
4715c004b256c513aa2af1f4e127e15ec7e011b0b4f4c1d0428d81a699e7fe0d9080B.
Source K4-END-COUNTER.candidate-v1.txt SHA
352c3b3d0fbd2d642acfe1537e42f88180dec4a0df58b99233ef43ac6bf0f208.
Manual finite7-position WF proof and ordinary Lean decide on<=3child parts;
no native_decide, generated certificate, new axiom, or proof failure.

Registration failuredef93361.3s/8359MiB: default ErdosSzekeres import had
118GiB olean closure above targeted4GiB guard. No lock/accepted node then.
Failed stub archived; es node add with exact unchanged type/doc and narrow
DecomposableContextLemmas import succeeded8da4f2,80.9s/2297MiB/OOM0.
Own ready claim/capture preceded proof. No extract bypass/full extraction.
es search for end-only k4 counterexample returned no hits.

Diagnostic ancestry: sampleeae2c6 with576 seeded rows/2880 classes and one
both-end miss; extract0ea5f8; exact replay7a5b7a old2/flip[1,2,2,2,1]; saved
interior query6b0094: all621 positive classes have an interior witness.
Artifacts k4-end-sample.json, k4-end-failures-extracted.json,
k4-end-failure-exact.json and k4-interior-witness-query.json. Separate
diagnostic code review CODE-REVIEW.0858.md. No universal inference.

Open obligation remains full positive any-length maximal-segment FLIP for
k>=4 at partiale03d9bc7. Zero-value exchange and k3 closed; k4 upper3 closed.
Next test sibling-max1 positivity under interior child addition, or prove
an interior exchange directly; retain arbitrary length/history coverage.
