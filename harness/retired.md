# Retired and refuted nodes

Append-only log written by `es node retire`.

## 2026-09-04 retired ErdosSzekeres.es_harness_conj

- reason: harness acceptance fixture (falsifier contract test)
- approved_by: fable
- statement: Eq 1 1
- module: ESBlueprint.G.EsHarnessConj
- kind: conjecture
- ws: G

## 2026-09-07 retired ErdosSzekeres.ctx_bound_additive_sandwich

- reason: Replace the unproved arbitrary-outer-length statement by a separately named singleton-outer sandwich lemma; fixed-coupling boundary reduction was falsified and no ancestry invariant is yet available.
- approved_by: codex:01a07c90-04b4-7703-a48c-d28d6db356a1-sandwich
- statement:

```
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
```

- module: ESBlueprint.B.CtxBoundAdditiveSandwich
- kind: formalization
- ws: B
