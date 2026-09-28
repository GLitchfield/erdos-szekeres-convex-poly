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
## 2026-09-07 retired ErdosSzekeres.ctx_bound_additive_sandwich
- reason: Replace the unproved arbitrary-outer-length statement by a separately named singleton-outer sandwich lemma; fixed-coupling boundary reduction was falsified and no ancestry invariant is yet available.
- approved_by: codex:01a07c90-04b4-7703-a48c-d28d6db356a1-sandwich
∀ (σ : ErdosSzekeres.Ctx.Context),
  σ.WellFormed →
    ∀ (b l m r : Nat),
      Eq σ.childPositions (List.range' b (instHAdd.hAdd (instHAdd.hAdd l m) r)) →
        instLTNat.lt 0 l →
          instLTNat.lt 0 m →
            instLTNat.lt 0 r →
              ∀ (d : Nat),
                instLENat.le 1 d →
                  instLENat.le d (instHSub.hSub σ.k 2) →
                    And
                      (instLENat.le
                        (instHAdd.hAdd
                          (σ.part
                              (instHAppendOfAppend.hAppend (List.range' b l)
                                (List.range' (instHAdd.hAdd (instHAdd.hAdd b l) m) r))
                              ErdosSzekeres.Ctx.Side.lower d).bound
                          (σ.part (List.range' (instHAdd.hAdd b l) m) ErdosSzekeres.Ctx.Side.upper
                              (instHSub.hSub (instHSub.hSub σ.k 1) d)).bound)
                        σ.bound)
                      (instLENat.le
                        (instHAdd.hAdd
                          (σ.part
                              (instHAppendOfAppend.hAppend (List.range' b l)
                                (List.range' (instHAdd.hAdd (instHAdd.hAdd b l) m) r))
                              ErdosSzekeres.Ctx.Side.upper
                              (instHSub.hSub (instHSub.hSub σ.k 1) d)).bound
                          (σ.part (List.range' (instHAdd.hAdd b l) m) ErdosSzekeres.Ctx.Side.lower
                              d).bound)
                        σ.bound)
- module: ESBlueprint.B.CtxBoundAdditiveSandwich
- kind: formalization

## 2026-09-16 retired ErdosSzekeres.CtxTwoMarkerYoungerExteriorInternalComplementChosenComponentFourBound

- reason: Immediate clerical correction: the declaration name was accidentally registered in CamelCase; it is being re-added with the repository-standard snake_case Lean name.
- approved_by: codex:agent-run-87535a41ec804a72
- statement:

```
∀ (σ : ErdosSzekeres.Ctx.Context),
  (∀ (p j : Nat) (v : ErdosSzekeres.Ctx.Side),
      Eq (σ.letterAt p) (ErdosSzekeres.Ctx.Letter.ext j v) → instLENat.le 1 j) →
    ∀ (s : ErdosSzekeres.Ctx.Side) (N M x y : Nat),
      List.instMembership.mem σ.levels N →
        List.instMembership.mem σ.levels M →
          instLTNat.lt N M →
            Eq (σ.sideAt N) s →
              Eq (σ.sideAt M) s →
                List.instMembership.mem (σ.extPositions N) x →
                  List.instMembership.mem (σ.extPositions M) y →
                    instLENat.le
                        (ErdosSzekeres.CtxTwoMarkerYoungerExteriorInternalComplementChosenComponentFourBound.match_1
                          (fun s => Nat) s (fun _ => σ.u) fun _ => σ.a)
                        5 →
                      (∀ (j : Nat),
                          List.instMembership.mem (σ.levelsOn s 0) j →
                            ∀ (p : Nat),
                              List.instMembership.mem (σ.extPositions j) p → Or (Eq p x) (Eq p y)) →
                        ∀ (keep : List Nat) (q₀ m : Nat),
                          List.instMembership.mem keep q₀ →
                            (∀ (p : Nat),
                                List.instMembership.mem keep p →
                                  List.instMembership.mem σ.childPositions p) →
                              (∀ (p : Nat),
                                  List.instMembership.mem keep p →
                                    ∀ (q : Nat),
                                      List.instMembership.mem keep q →
                                        ∀ (z : Nat),
                                          List.instMembership.mem σ.childPositions z →
                                            instLENat.le p z →
                                              instLENat.le z q → List.instMembership.mem keep z) →
                                Or
                                    (And (instLTNat.lt x y)
                                      (∀ (p : Nat),
                                        List.instMembership.mem keep p → instLTNat.lt p x))
                                    (And (instLTNat.lt y x)
                                      (∀ (p : Nat),
                                        List.instMembership.mem keep p → instLTNat.lt x p)) →
                                  have rest :=
                                    List.filter
                                      (fun x =>
                                        Decidable.decide (Not (List.instMembership.mem keep x)))
                                      σ.childPositions;
                                  And
                                    (∀ (fuel : Nat),
                                      instLENat.le
                                        (ErdosSzekeres.Ctx.Context.boundFuel fuel (σ.part rest s m))
                                        4)
                                    (instLENat.le (σ.part rest s m).bound 4)
```

- module: ESBlueprint.B.CtxTwoMarkerYoungerExteriorInternalComplementChosenComponentFourBound
- kind: formalization
- ws: B

## 2026-09-16 retired ErdosSzekeres.CtxTwoMarkerYoungerExteriorInternalComplementChosenComponentFourBound

- reason: Immediate clerical correction: the declaration name was accidentally registered in CamelCase; it is being re-added with the repository-standard snake_case Lean name.
- approved_by: codex:agent-run-87535a41ec804a72
- statement:

```
∀ (σ : ErdosSzekeres.Ctx.Context),
  (∀ (p j : Nat) (v : ErdosSzekeres.Ctx.Side),
      Eq (σ.letterAt p) (ErdosSzekeres.Ctx.Letter.ext j v) → instLENat.le 1 j) →
    ∀ (s : ErdosSzekeres.Ctx.Side) (N M x y : Nat),
      List.instMembership.mem σ.levels N →
        List.instMembership.mem σ.levels M →
          instLTNat.lt N M →
            Eq (σ.sideAt N) s →
              Eq (σ.sideAt M) s →
                List.instMembership.mem (σ.extPositions N) x →
                  List.instMembership.mem (σ.extPositions M) y →
                    instLENat.le
                        (ErdosSzekeres.CtxTwoMarkerYoungerExteriorInternalComplementChosenComponentFourBound.match_1
                          (fun s => Nat) s (fun _ => σ.u) fun _ => σ.a)
                        5 →
                      (∀ (j : Nat),
                          List.instMembership.mem (σ.levelsOn s 0) j →
                            ∀ (p : Nat),
                              List.instMembership.mem (σ.extPositions j) p → Or (Eq p x) (Eq p y)) →
                        ∀ (keep : List Nat) (q₀ m : Nat),
                          List.instMembership.mem keep q₀ →
                            (∀ (p : Nat),
                                List.instMembership.mem keep p →
                                  List.instMembership.mem σ.childPositions p) →
                              (∀ (p : Nat),
                                  List.instMembership.mem keep p →
                                    ∀ (q : Nat),
                                      List.instMembership.mem keep q →
                                        ∀ (z : Nat),
                                          List.instMembership.mem σ.childPositions z →
                                            instLENat.le p z →
                                              instLENat.le z q → List.instMembership.mem keep z) →
                                Or
                                    (And (instLTNat.lt x y)
                                      (∀ (p : Nat),
                                        List.instMembership.mem keep p → instLTNat.lt p x))
                                    (And (instLTNat.lt y x)
                                      (∀ (p : Nat),
                                        List.instMembership.mem keep p → instLTNat.lt x p)) →
                                  have rest :=
                                    List.filter
                                      (fun x =>
                                        Decidable.decide (Not (List.instMembership.mem keep x)))
                                      σ.childPositions;
                                  And
                                    (∀ (fuel : Nat),
                                      instLENat.le
                                        (ErdosSzekeres.Ctx.Context.boundFuel fuel (σ.part rest s m))
                                        4)
                                    (instLENat.le (σ.part rest s m).bound 4)
```

- module: ESBlueprint.B.CtxTwoMarkerYoungerExteriorInternalComplementChosenComponentFourBound
- kind: formalization
- ws: B
