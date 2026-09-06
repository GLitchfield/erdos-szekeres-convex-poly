module

public import ErdosSzekeres.DecomposableRealization

@[expose] public section

/-!
# Contexts of subtrees in a decomposition tree (Workstream B)

The induction state for the decomposable-set theorem, experiments 0117 to
0121.  A subtree `S` of a decomposition tree sees the rest of the coloring as
a *context*: the sweep-order word of `S`'s own vertices and of the external
vertices, each external vertex tagged by its level along `S`'s path to the
root (level 1 is the nearest ancestor split) and by the side of `S` at that
split, together with each level's sibling chain maximum.  From the context
alone, two rules bound every chain and strong set of `S`: chains grow by one
vertex per side per level, taken as a longest chain of levels with positions
moving outward (`leftExt`, `rightExt`), and strong sets join a sibling's
longest chain at exactly one level after extending through the levels below
it (`joinExt`).  `bound` is the recursion of experiment 0120 with the
interval cuts of experiment 0121: a single run is bounded by the classical
threshold with its internal parameters; otherwise one part is any contiguous
block of the child's letters, the other part the rest, in either
orientation, coupled through the two new sibling maxima.

Everything here is computable; the conjectured lemma is `bound_additive`
(Workstream B node), whose falsifier is `scripts/decomposable_additivity_test.py`.
-/

namespace ErdosSzekeres
namespace Ctx

/-- The side of the child at an ancestor split. -/
inductive Side where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- A letter of a context word: one child vertex, or one external vertex tagged by its
level along the child's path (1 = the nearest ancestor split) and the child's side there. -/
inductive Letter where
  | child
  | ext (level : ℕ) (side : Side)
  deriving DecidableEq, Repr

/-- A context for the parameters `(a, u, k)`: the word in sweep order and, for each level
`l ≥ 1`, the longest chain of the sibling at that level (`maxima[l-1]`; a cap when the
child is lower there, a cup when it is upper). -/
structure Context where
  a : ℕ
  u : ℕ
  k : ℕ
  word : List Letter
  maxima : List ℕ
  deriving Repr

namespace Context

/-- The letter at a position (`child` beyond the word, harmless). -/
def letterAt (σ : Context) (p : ℕ) : Letter :=
  (σ.word[p]?).getD Letter.child

/-- Positions of the child's vertices, in sweep order. -/
def childPositions (σ : Context) : List ℕ :=
  (List.range σ.word.length).filter fun p => σ.letterAt p = Letter.child

/-- Positions of the external vertices of a level. -/
def extPositions (σ : Context) (l : ℕ) : List ℕ :=
  (List.range σ.word.length).filter fun p =>
    match σ.letterAt p with
    | Letter.ext l' _ => l' = l
    | _ => False

/-- The child's side at a level (`lower` when the level has no letter). -/
def sideAt (σ : Context) (l : ℕ) : Side :=
  match (σ.extPositions l).head? with
  | some p =>
      match σ.letterAt p with
      | Letter.ext _ s => s
      | _ => Side.lower
  | none => Side.lower

/-- The levels present, `1 .. maxima.length`. -/
def levels (σ : Context) : List ℕ :=
  (List.range σ.maxima.length).map (· + 1)

/-- The sibling chain maximum at a level. -/
def maximumAt (σ : Context) (l : ℕ) : ℕ :=
  (σ.maxima[l - 1]?).getD 0

/-- Number of runs (maximal blocks of child letters). -/
def numRuns (σ : Context) : ℕ :=
  ((List.range σ.word.length).filter fun p =>
    σ.letterAt p = Letter.child ∧ (p = 0 ∨ σ.letterAt (p - 1) ≠ Letter.child)).length

/-- The levels at which the child sits on the given side, below level `top`
(`top = 0` means all levels). -/
def levelsOn (σ : Context) (s : Side) (top : ℕ) : List ℕ :=
  σ.levels.filter fun l => σ.sideAt l = s ∧ (top = 0 ∨ l < top)

/-- Left extension count of a chain whose first vertex is at position `p`, using the
levels on side `s` below `top`: the longest sequence of levels `l₁ < l₂ < …` with one
external vertex each, all left of `p`, positions moving outward (decreasing).  Enumerated
as a sublist of the levels, each level contributing its rightmost letter left of the
current end. -/
def leftExt (σ : Context) (s : Side) (top : ℕ) (p : ℕ) : ℕ :=
  let step : ℕ × ℕ → ℕ → ℕ × ℕ := fun (endPos, count) l =>
    match ((σ.extPositions l).filter (· < endPos)).getLast? with
    | some x => (x, count + 1)
    | none => (endPos, count)
  (((σ.levelsOn s top).sublists.map fun ls => (ls.foldl step (p, 0)).2).max?).getD 0

/-- Right extension count, mirror image of `leftExt`. -/
def rightExt (σ : Context) (s : Side) (top : ℕ) (p : ℕ) : ℕ :=
  let step : ℕ × ℕ → ℕ → ℕ × ℕ := fun (endPos, count) l =>
    match ((σ.extPositions l).filter (endPos < ·)).head? with
    | some x => (x, count + 1)
    | none => (endPos, count)
  (((σ.levelsOn s top).sublists.map fun ls => (ls.foldl step (p, 0)).2).max?).getD 0

/-- Chain extension of a chain of side-type `s` from position `p` to position `q`. -/
def chainExt (σ : Context) (s : Side) (p q : ℕ) : ℕ :=
  σ.leftExt s 0 p + σ.rightExt s 0 q

/-- Strong-set extension: extend through the levels below `N`, then join the sibling's
longest chain at `N`; or the pure chain extension. -/
def joinExt (σ : Context) (s : Side) (p q : ℕ) : ℕ :=
  max (σ.chainExt s p q)
    ((((σ.levelsOn s 0).map fun N =>
        σ.leftExt s N p + σ.rightExt s N q + σ.maximumAt N).max?).getD 0)

/-- Largest cup allowed from position `p` to position `q` (0 = no vertex may sit there). -/
def cupLimit (σ : Context) (p q : ℕ) : ℕ :=
  min (σ.u - 1 - σ.chainExt Side.lower p q) (σ.k - 1 - σ.joinExt Side.lower p q)

/-- Largest cap allowed from position `p` to position `q`. -/
def capLimit (σ : Context) (p q : ℕ) : ℕ :=
  min (σ.a - 1 - σ.chainExt Side.upper p q) (σ.k - 1 - σ.joinExt Side.upper p q)

/-- The context of a part of the child: the kept positions stay child letters, the other
child positions become external letters of a new level 1 on which the part is on side
`s`, every old level shifts by one, and the new sibling's chain maximum is `m`. -/
def part (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) : Context where
  a := σ.a
  u := σ.u
  k := σ.k
  word := (List.range σ.word.length).map fun p =>
    match σ.letterAt p with
    | Letter.child => if p ∈ keep then Letter.child else Letter.ext 1 s
    | Letter.ext l s' => Letter.ext (l + 1) s'
  maxima := m :: σ.maxima

/-- The base value of a single run: the classical threshold with the run's internal
parameters (with the conventions for limits of 0 and 1). -/
def base (σ : Context) : ℕ :=
  match σ.childPositions.head? with
  | none => 0
  | some p =>
      let cl := σ.cupLimit p p
      let pl := σ.capLimit p p
      if cl = 0 ∨ pl = 0 then 0
      else if cl = 1 ∨ pl = 1 then 1
      else decomposableThreshold (pl + 1) (cl + 1) σ.k

/-- All contiguous blocks of the child positions other than the whole. -/
def blocks (σ : Context) : List (List ℕ) :=
  let ps := σ.childPositions
  ((List.range ps.length).flatMap fun i =>
    (List.range (ps.length - i)).map fun len => (ps.drop i).take (len + 1)).filter
      fun b => b.length < ps.length

/-- The recursion with fuel (structural on `fuel`; `bound` supplies enough). -/
def boundFuel : ℕ → Context → ℕ
  | 0, _ => 0
  | fuel + 1, σ =>
      if σ.numRuns ≤ 1 then σ.base
      else
        let ps := σ.childPositions
        let cuts := σ.blocks.flatMap fun block =>
          let rest := ps.filter (· ∉ block)
          (List.range (σ.k - 2)).flatMap fun d' =>
            let dp := d' + 1
            let c := σ.k - 1 - dp
            [ boundFuel fuel (σ.part block Side.lower dp) + boundFuel fuel (σ.part rest Side.upper c),
              boundFuel fuel (σ.part block Side.upper c) + boundFuel fuel (σ.part rest Side.lower dp) ]
        (cuts.max?).getD 0

/-- The child bound of a context: the recursion of experiments 0120/0121 with interval cuts.
Cuts with a part whose bound is 0 contribute 0, as in the reference implementation. -/
def bound (σ : Context) : ℕ :=
  boundFuel (σ.childPositions.length + 1) σ

end Context

open Classical in
/-- The longest cup (`left = true`) or cap contained in `s`. -/
noncomputable def chainMax {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n)) (left : Bool) : ℕ :=
  (s.powerset.filter fun t => if left then IsCupSet χ t else IsCapSet χ t).sup Finset.card

/-- `χ` restricted to `S` satisfies the context `σ`: the child letters of `σ` are the
vertices of `S` in sweep order, and every cup, cap and strong set of `S` obeys the
limits of `σ` at the positions of its first and last vertex. -/
def Satisfies {n : ℕ} (χ : TripleColoring n) (S : Finset (Fin n)) (σ : Context) : Prop :=
  σ.childPositions.length = S.card ∧
  ∀ C : Finset (Fin n), C ⊆ S → ∀ hC : C.Nonempty,
    let pos : Fin n → ℕ := fun v => (σ.childPositions[(S.filter (· < v)).card]?).getD 0
    (IsCupSet χ C → C.card ≤ σ.cupLimit (pos (C.min' hC)) (pos (C.max' hC))) ∧
    (IsCapSet χ C → C.card ≤ σ.capLimit (pos (C.min' hC)) (pos (C.max' hC))) ∧
    (IsStrongPolygonSet χ C → C.card ≤ σ.k - 1)

/-- The root context of a child of `s` vertices: no external vertex. -/
def Context.root (a u k s : ℕ) : Context :=
  ⟨a, u, k, List.replicate s Letter.child, []⟩

/-- The child positions of `σ` occupied by the vertices of `part ⊆ S` (the `i`-th vertex
of `S` in sweep order sits at the `i`-th child position). -/
def Context.positionsOf {n : ℕ} (σ : Context) (S part : Finset (Fin n)) : List ℕ :=
  (part.image fun v => (σ.childPositions[(S.filter (· < v)).card]?).getD 0).sort (· ≤ ·)

/-- The context with the sibling maximum at level `l` replaced by `m`. -/
def Context.withMaximum (σ : Context) (l m : ℕ) : Context :=
  { σ with maxima := σ.maxima.set (l - 1) m }

/-- Well-formed contexts: the parameters of a case, sibling maxima in `1 .. k-2`, external
letters at levels `1 .. maxima.length`, one side per level. -/
def Context.WellFormed (σ : Context) : Prop :=
  2 ≤ σ.a ∧ 2 ≤ σ.u ∧ σ.a ≤ σ.k ∧ σ.u ≤ σ.k ∧
  (∀ m ∈ σ.maxima, 1 ≤ m ∧ m ≤ σ.k - 2) ∧
  (∀ p l s, σ.letterAt p = Letter.ext l s → 1 ≤ l ∧ l ≤ σ.maxima.length ∧ s = σ.sideAt l)

end Ctx
end ErdosSzekeres

end
