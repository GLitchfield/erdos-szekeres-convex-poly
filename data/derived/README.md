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
