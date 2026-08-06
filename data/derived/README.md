# Derived evidence

Store compact committed results and independently checkable certificates here.
Large checkpoints, incomplete runs, caches, and machine-local logs belong under
ignored `runs/`.

- `e3-context-k6-n9-singleton-collision.json` is the compact all-gap profile
  incompleteness witness produced by
  `scripts/find_decomposable_context_collision.py` at source revision
  `180b1cb2da36bab489561682773c850cd6a09c3c`.  Its independent checker is
  `scripts/check_decomposable_context_collision.py`; the certificate SHA-256
  is `2a7a7930d4e68b0c9836076c0ec9f5573ba3af56cca577e6f17162d892f2a142`.
- `e3-singleton-residual-k6-n9.json` records the exact property-relative
  residual classes of all eight-vertex decomposable colorings under all 18
  singleton root contexts. Its independent checker is
  `scripts/check_singleton_residuals.py`; the large observation tables stay
  under ignored `runs/`.
- `e3-span-rank-footprint-k6-n9.json` records the exact endpoint-span rank
  footprint gate on the same colorings and contexts. It covers 3,363,984
  singleton extensions, with zero observation-readout mismatches and zero
  footprint-transition collisions. Its independent checker is
  `scripts/check_span_rank_footprints.py`; the 119 MiB parent tables stay
  under ignored `runs/`. The manifest SHA-256 is
  `74a0d2bb8de0419d51921d2c2edcb4a30532e1fde4d8a210743b7a86c414d12a`.
- `e3-two-root-span-k6-n9.json` records the next interleaved-root gate for the
  endpoint-span footprint. It covers all 10,596 decomposable seven-vertex
  children, all 72 placements and roles of a two-vertex root, and 762,912
  parent transitions. Of those, 720,528 transitions use one of the 68
  nontrivially interleaved contexts. The independent checker finds zero
  observation-readout mismatches and zero footprint-transition collisions.
  Its manifest SHA-256 is
  `70d5f08c0bce7fb0ae7ef0748c59a19e81f0c1d002e077aa727877f4794b8a33`.
- `e3-allocated-span-pascal-demand-k6-n8.json` records every compatible
  decomposition root on every labeled support through eight vertices at
  `k = 6`. Across 631,474 open exact-rank frontier groups, no two-sided
  interval frontier exceeds `choose(4, rank - 1)`. The independent checker
  reproduces every count, sharp rank-five example, canonical digest, and the
  falsification of direct cup--cap on either endpoint projection. Each
  projection fails in 1,208 groups, and 996 rank-three groups fail both. This
  is bounded evidence for a local capacity lemma and against one proposed
  proof, not a proof of the general inequality or of a global Pascal-window
  injection. Its manifest SHA-256 is
  `6bd8341ee26511daf73d2c38a8634086ba2fdca037988a4bb83083aec95d0313`.
- `e3-reflected-transition-hall-k6-n8.json` records the first bounded gate for
  orientation-reflected endpoint-transition candidates. Rotate-complement is
  applied exactly when a span's left endpoint belongs to the upper child, and
  both orientations still use the same untagged Pascal carrier. The frozen
  `n = 12`, `k = 7` root frontier passes, with the former rigid pair separated
  as full versus empty ideals. Both independent representations then find no
  Hall failure among all 631,474 `k = 6` groups through eight vertices and no
  same-orientation rigid pair, reflection-fixed opposite pair, or triple-rigid
  collision. This is bounded evidence only, not a general Hall theorem.
  Its manifest SHA-256 is
  `f65c400c9b99f944eb755f5ea3d38e47adf94f9a25737e56401fec1af263c267`.
