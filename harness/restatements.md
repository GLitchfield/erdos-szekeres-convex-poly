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

## 2026-09-15 restate ErdosSzekeres.ctx_two_marker_older_exterior_endpoint_cut_six_bound

- approved_by: codex:agent-run-0ce68047e38845f0
- reason: The first draft omitted the existing endpoint theorem and consumer premise 2 ≤ opposite width; make that required rank-window hypothesis explicit before proof work.
- old_type_hash: 8e2b56be82d511dd
- new_type_hash: f034d2b8abb7e6d3
- old:

```
∀ (σ : ErdosSzekeres.Ctx.Context),
  (∀ (p j : Nat) (v : ErdosSzekeres.Ctx.Side),
      Eq (σ.letterAt p) (ErdosSzekeres.Ctx.Letter.ext j v) → instLENat.le 1 j) →
    ∀ (s t : ErdosSzekeres.Ctx.Side),
      Ne s t →
        ∀ (N M x y : Nat),
          List.instMembership.mem σ.levels N →
            List.instMembership.mem σ.levels M →
              instLTNat.lt N M →
                Eq (σ.sideAt N) s →
                  Eq (σ.sideAt M) s →
                    List.instMembership.mem (σ.extPositions N) x →
                      List.instMembership.mem (σ.extPositions M) y →
                        instLENat.le
                            (ErdosSzekeres.ctx_two_marker_older_exterior_endpoint_cut_six_bound.match_1
                              (fun s => Nat) s (fun _ => σ.u) fun _ => σ.a)
                            5 →
                          instLENat.le
                              (ErdosSzekeres.ctx_two_marker_older_exterior_endpoint_cut_six_bound.match_1
                                (fun t => Nat) t (fun _ => σ.u) fun _ => σ.a)
                              5 →
                            Eq (σ.levelsOn t 0) List.nil →
                              ∀ (keep : List Nat) (q₀ l m n : Nat),
                                List.instMembership.mem keep q₀ →
                                  (∀ (p : Nat),
                                      List.instMembership.mem keep p →
                                        List.instMembership.mem σ.childPositions p) →
                                    List.instMembership.mem σ.childPositions l →
                                      Not (List.instMembership.mem keep l) →
                                        Or
                                            (And
                                              (∀ (p : Nat),
                                                List.instMembership.mem keep p → instLTNat.lt y p)
                                              (And (instLTNat.lt x y)
                                                (∀ (p : Nat),
                                                  List.instMembership.mem keep p →
                                                    ∀ (q : Nat),
                                                      List.instMembership.mem σ.childPositions q →
                                                        Not (List.instMembership.mem keep q) →
                                                          instLTNat.lt q p)))
                                            (And
                                              (∀ (p : Nat),
                                                List.instMembership.mem keep p → instLTNat.lt p y)
                                              (And (instLTNat.lt y x)
                                                (∀ (p : Nat),
                                                  List.instMembership.mem keep p →
                                                    ∀ (q : Nat),
                                                      List.instMembership.mem σ.childPositions q →
                                                        Not (List.instMembership.mem keep q) →
                                                          instLTNat.lt p q))) →
                                          Eq σ.k 6 →
                                            instLENat.le 1 m →
                                              instLENat.le 1 n →
                                                Eq (instHAdd.hAdd m n) (instHSub.hSub σ.k 1) →
                                                  have rest :=
                                                    List.filter
                                                      (fun x =>
                                                        Decidable.decide
                                                          (Not (List.instMembership.mem keep x)))
                                                      σ.childPositions;
                                                  And
                                                    (∀ (f g : Nat),
                                                      instLENat.le
                                                        (instHAdd.hAdd
                                                          (ErdosSzekeres.Ctx.Context.boundFuel f
                                                            (σ.part rest s m))
                                                          (ErdosSzekeres.Ctx.Context.boundFuel g
                                                            (σ.part keep t n)))
                                                        12)
                                                    (instLENat.le
                                                      (instHAdd.hAdd (σ.part rest s m).bound
                                                        (σ.part keep t n).bound)
                                                      12)
```

- new:

```
∀ (σ : ErdosSzekeres.Ctx.Context),
  (∀ (p j : Nat) (v : ErdosSzekeres.Ctx.Side),
      Eq (σ.letterAt p) (ErdosSzekeres.Ctx.Letter.ext j v) → instLENat.le 1 j) →
    ∀ (s t : ErdosSzekeres.Ctx.Side),
      Ne s t →
        ∀ (N M x y : Nat),
          List.instMembership.mem σ.levels N →
            List.instMembership.mem σ.levels M →
              instLTNat.lt N M →
                Eq (σ.sideAt N) s →
                  Eq (σ.sideAt M) s →
                    List.instMembership.mem (σ.extPositions N) x →
                      List.instMembership.mem (σ.extPositions M) y →
                        instLENat.le
                            (ErdosSzekeres.ctx_two_marker_older_exterior_endpoint_cut_six_bound.match_1
                              (fun s => Nat) s (fun _ => σ.u) fun _ => σ.a)
                            5 →
                          instLENat.le
                              (ErdosSzekeres.ctx_two_marker_older_exterior_endpoint_cut_six_bound.match_1
                                (fun t => Nat) t (fun _ => σ.u) fun _ => σ.a)
                              5 →
                            instLENat.le 2
                                (instHSub.hSub
                                  (ErdosSzekeres.ctx_two_marker_older_exterior_endpoint_cut_six_bound.match_1
                                    (fun t => Nat) t (fun _ => σ.u) fun _ => σ.a)
                                  1) →
                              Eq (σ.levelsOn t 0) List.nil →
                                ∀ (keep : List Nat) (q₀ l m n : Nat),
                                  List.instMembership.mem keep q₀ →
                                    (∀ (p : Nat),
                                        List.instMembership.mem keep p →
                                          List.instMembership.mem σ.childPositions p) →
                                      List.instMembership.mem σ.childPositions l →
                                        Not (List.instMembership.mem keep l) →
                                          Or
                                              (And
                                                (∀ (p : Nat),
                                                  List.instMembership.mem keep p → instLTNat.lt y p)
                                                (And (instLTNat.lt x y)
                                                  (∀ (p : Nat),
                                                    List.instMembership.mem keep p →
                                                      ∀ (q : Nat),
                                                        List.instMembership.mem σ.childPositions q →
                                                          Not (List.instMembership.mem keep q) →
                                                            instLTNat.lt q p)))
                                              (And
                                                (∀ (p : Nat),
                                                  List.instMembership.mem keep p → instLTNat.lt p y)
                                                (And (instLTNat.lt y x)
                                                  (∀ (p : Nat),
                                                    List.instMembership.mem keep p →
                                                      ∀ (q : Nat),
                                                        List.instMembership.mem σ.childPositions q →
                                                          Not (List.instMembership.mem keep q) →
                                                            instLTNat.lt p q))) →
                                            Eq σ.k 6 →
                                              instLENat.le 1 m →
                                                instLENat.le 1 n →
                                                  Eq (instHAdd.hAdd m n) (instHSub.hSub σ.k 1) →
                                                    have rest :=
                                                      List.filter
                                                        (fun x =>
                                                          Decidable.decide
                                                            (Not (List.instMembership.mem keep x)))
                                                        σ.childPositions;
                                                    And
                                                      (∀ (f g : Nat),
                                                        instLENat.le
                                                          (instHAdd.hAdd
                                                            (ErdosSzekeres.Ctx.Context.boundFuel f
                                                              (σ.part rest s m))
                                                            (ErdosSzekeres.Ctx.Context.boundFuel g
                                                              (σ.part keep t n)))
                                                          12)
                                                      (instLENat.le
                                                        (instHAdd.hAdd (σ.part rest s m).bound
                                                          (σ.part keep t n).bound)
                                                        12)
```
