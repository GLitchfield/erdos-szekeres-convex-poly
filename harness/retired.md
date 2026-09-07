# Retired and refuted nodes

Append-only log written by `es node retire`.

## 2026-09-04 retired ErdosSzekeres.es_harness_conj

- reason: harness acceptance fixture (falsifier contract test)
- approved_by: fable
- statement: Eq 1 1
- module: ESBlueprint.G.EsHarnessConj
- kind: conjecture
- ws: G

## 2026-09-07 retired ErdosSzekeres.ctx_bound_exchange_orientation_counterexample

- reason: The provisional three-child witness has an interval complement and therefore is already covered by ctx_bound_cut_le; it is retained only in the finite probe, while this one-node branch will formalize the general interval-or-complement normalization that isolates genuine crossing.
- approved_by: codex:01a07c5a-4a94-7173-865c-d990c69ab997-exchange
- statement:

```
have σ :=
  { a := 4, u := 4, k := 5,
    word :=
      List.cons ErdosSzekeres.Ctx.Letter.child
        (List.cons (ErdosSzekeres.Ctx.Letter.ext 1 ErdosSzekeres.Ctx.Side.lower)
          (List.cons ErdosSzekeres.Ctx.Letter.child
            (List.cons ErdosSzekeres.Ctx.Letter.child List.nil))),
    maxima := List.cons 1 List.nil };
have keep := List.cons 0 (List.cons 3 List.nil);
have lowerValue := fun block =>
  instHAdd.hAdd (σ.part block ErdosSzekeres.Ctx.Side.lower 1).bound
    (σ.part
        (List.filter (fun p => Decidable.decide (Not (List.instMembership.mem block p)))
          σ.childPositions)
        ErdosSzekeres.Ctx.Side.upper 3).bound;
have upperValue := fun block =>
  instHAdd.hAdd (σ.part block ErdosSzekeres.Ctx.Side.upper 3).bound
    (σ.part
        (List.filter (fun p => Decidable.decide (Not (List.instMembership.mem block p)))
          σ.childPositions)
        ErdosSzekeres.Ctx.Side.lower 1).bound;
And σ.WellFormed
  (And (Eq σ.childPositions (List.cons 0 (List.cons 2 (List.cons 3 List.nil))))
    (And (Eq σ.numRuns 2)
      (And (Not (List.instMembership.mem σ.blocks keep))
        (And (Eq (lowerValue keep) 5)
          (And
            (∀ (block : List Nat),
              List.instMembership.mem σ.blocks block → instLENat.le (lowerValue block) 4)
            (And
              (Exists fun block =>
                And (List.instMembership.mem σ.blocks block) (Eq (upperValue block) 5))
              (Eq σ.bound 5)))))))
```

- module: ESBlueprint.B.CtxBoundExchangeOrientationCounterexample
- kind: refutation
- ws: B
