# Restatements

Append-only log written by `es node restate`. Each entry records the node, the
old and new statement, who approved it, and why.

## 2026-09-04 restate ErdosSzekeres.es_harness_smoke

- approved_by: fable (smoke test)
- reason: acceptance test 4
- old_type_hash: b9486272e56c970d
- new_type_hash: 506a3f29a56aa2c5
- old: Eq (instHAdd.hAdd 2 2) 4
- new: Eq (instHAdd.hAdd 3 3) 6
