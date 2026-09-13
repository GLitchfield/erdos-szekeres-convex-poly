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

## 2026-09-13 restate ErdosSzekeres.ctx_nonmonotone_triple_small_maxima_counterexample

- approved_by: codex:01a090b8-9c6d-70a0-be04-e9e824a70bc5
- reason: Replace exact bound equality with the sufficient lower-bound certificate after the preserved exact-statement 3G and 8G kernel checks exhausted memory.
- old_type_hash: c656ec0b86d4f5ac
- new_type_hash: 7eaa5ea071400f69
- old:

```
have σ :=
  { a := 6, u := 5, k := 6,
    word :=
      List.cons ErdosSzekeres.Ctx.Letter.child
        (List.cons ErdosSzekeres.Ctx.Letter.child
          (List.cons (ErdosSzekeres.Ctx.Letter.ext 1 ErdosSzekeres.Ctx.Side.lower)
            (List.cons ErdosSzekeres.Ctx.Letter.child
              (List.cons (ErdosSzekeres.Ctx.Letter.ext 3 ErdosSzekeres.Ctx.Side.lower)
                (List.cons (ErdosSzekeres.Ctx.Letter.ext 2 ErdosSzekeres.Ctx.Side.lower)
                  (List.cons ErdosSzekeres.Ctx.Letter.child List.nil)))))),
    maxima := List.cons 1 (List.cons 1 (List.cons 1 List.nil)) };
And σ.WellFormed
  (And (Eq σ.levels (List.cons 1 (List.cons 2 (List.cons 3 List.nil))))
    (And (Eq (σ.levelsOn ErdosSzekeres.Ctx.Side.upper 0) List.nil)
      (And (Eq (σ.extPositions 1) (List.cons 2 List.nil))
        (And (Eq (σ.extPositions 2) (List.cons 5 List.nil))
          (And (Eq (σ.extPositions 3) (List.cons 4 List.nil))
            (And
              (∀ (j : Nat),
                List.instMembership.mem σ.levels j →
                  And (Eq (σ.sideAt j) ErdosSzekeres.Ctx.Side.lower)
                    (instLTNat.lt (σ.maximumAt j) (instHSub.hSub σ.k 4)))
              (And (Eq σ.bound 11) (Eq (instHSub.hSub (instHMul.hMul 3 σ.k) 8) 10))))))))
```

- new:

```
have σ :=
  { a := 6, u := 5, k := 6,
    word :=
      List.cons ErdosSzekeres.Ctx.Letter.child
        (List.cons ErdosSzekeres.Ctx.Letter.child
          (List.cons (ErdosSzekeres.Ctx.Letter.ext 1 ErdosSzekeres.Ctx.Side.lower)
            (List.cons ErdosSzekeres.Ctx.Letter.child
              (List.cons (ErdosSzekeres.Ctx.Letter.ext 3 ErdosSzekeres.Ctx.Side.lower)
                (List.cons (ErdosSzekeres.Ctx.Letter.ext 2 ErdosSzekeres.Ctx.Side.lower)
                  (List.cons ErdosSzekeres.Ctx.Letter.child List.nil)))))),
    maxima := List.cons 1 (List.cons 1 (List.cons 1 List.nil)) };
And σ.WellFormed
  (And (Eq σ.levels (List.cons 1 (List.cons 2 (List.cons 3 List.nil))))
    (And (Eq (σ.levelsOn ErdosSzekeres.Ctx.Side.upper 0) List.nil)
      (And (Eq (σ.extPositions 1) (List.cons 2 List.nil))
        (And (Eq (σ.extPositions 2) (List.cons 5 List.nil))
          (And (Eq (σ.extPositions 3) (List.cons 4 List.nil))
            (And
              (∀ (j : Nat),
                List.instMembership.mem σ.levels j →
                  And (Eq (σ.sideAt j) ErdosSzekeres.Ctx.Side.lower)
                    (instLTNat.lt (σ.maximumAt j) (instHSub.hSub σ.k 4)))
              (And (instLENat.le 11 σ.bound) (Eq (instHSub.hSub (instHMul.hMul 3 σ.k) 8) 10))))))))
```
