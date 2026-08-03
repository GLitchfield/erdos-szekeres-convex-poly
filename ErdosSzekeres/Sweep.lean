module

public import ErdosSzekeres.Basic

@[expose] public section

/-!
# Sweeps and the left/right triple coloring

We normalize the user's generic sweep direction to the first coordinate.  A
future public-to-sweep bridge will justify this normalization for an arbitrary
finite point set.  For a fixed index order, the orientation-sign convention is
preserved by orientation-preserving affine maps; the ordering itself is part of
the normalized data here.
-/

namespace ErdosSzekeres

noncomputable section

/-- The two possible turns made by three non-collinear points. -/
inductive Turn where
  | left
  | right
  deriving DecidableEq, Repr

/-- Three increasing indices, i.e. one edge of the ordered complete
3-uniform hypergraph. -/
structure OrderedTriple (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  hij : i < j
  hjk : j < k

/-- A two-coloring of all increasing triples. -/
abbrev TripleColoring (n : ℕ) := OrderedTriple n → Turn

namespace OrderedTriple

/-- Relabel an ordered triple along an increasing embedding. -/
def map {m n : ℕ} (f : Fin m ↪o Fin n) (t : OrderedTriple m) : OrderedTriple n :=
  ⟨f t.i, f t.j, f t.k, f.strictMono t.hij, f.strictMono t.hjk⟩

@[simp] theorem map_i {m n : ℕ} (f : Fin m ↪o Fin n) (t : OrderedTriple m) :
    (t.map f).i = f t.i := rfl

@[simp] theorem map_j {m n : ℕ} (f : Fin m ↪o Fin n) (t : OrderedTriple m) :
    (t.map f).j = f t.j := rfl

@[simp] theorem map_k {m n : ℕ} (f : Fin m ↪o Fin n) (t : OrderedTriple m) :
    (t.map f).k = f t.k := rfl

end OrderedTriple

namespace TripleColoring

/-- Restrict a triple coloring to an increasingly relabeled subset. -/
def restrict {m n : ℕ} (χ : TripleColoring n) (f : Fin m ↪o Fin n) :
    TripleColoring m :=
  fun t => χ (t.map f)

@[simp] theorem restrict_apply {m n : ℕ} (χ : TripleColoring n)
    (f : Fin m ↪o Fin n) (t : OrderedTriple m) :
    χ.restrict f t = χ (t.map f) :=
  rfl

end TripleColoring

/-- A point configuration already indexed in the order encountered by a
generic sweep.  After choosing the sweep direction as the first coordinate,
genericity says that this coordinate is strictly increasing. -/
structure SweptConfiguration (n : ℕ) where
  point : Fin n → Point 2
  sweep_strictMono : StrictMono fun i => point i 0
  generalPosition : ∀ ⦃i j k : Fin n⦄,
    i ≠ j → i ≠ k → j ≠ k → orientation (point i) (point j) (point k) ≠ 0

namespace SweptConfiguration

variable {n : ℕ} (P : SweptConfiguration n)

/-- A generic sweep labels distinct points injectively. -/
theorem point_injective : Function.Injective P.point := by
  intro i j hij
  exact P.sweep_strictMono.injective (congrFun hij 0)

/-- Restrict a swept configuration along an increasing embedding of indices. -/
def restrict {m : ℕ} (f : Fin m ↪o Fin n) : SweptConfiguration m where
  point := P.point ∘ f
  sweep_strictMono := P.sweep_strictMono.comp f.strictMono
  generalPosition := by
    intro i j k hij hik hjk
    exact P.generalPosition (f.injective.ne hij) (f.injective.ne hik)
      (f.injective.ne hjk)

@[simp] theorem restrict_point {m : ℕ} (f : Fin m ↪o Fin n) (i : Fin m) :
    (P.restrict f).point i = P.point (f i) :=
  rfl

/-- The turn made by any three indexed points.  General position makes the
`otherwise` branch genuinely right for distinct indices. -/
def turn (i j k : Fin n) : Turn :=
  if 0 < orientation (P.point i) (P.point j) (P.point k) then
    Turn.left
  else
    Turn.right

/-- Forget the coordinates but retain the left/right label of every increasing
triple. -/
def tripleColoring : TripleColoring n := fun t => P.turn t.i t.j t.k

/-- Restricting a swept configuration restricts its induced coloring by the
same increasing relabeling. -/
@[simp] theorem restrict_tripleColoring_apply {m : ℕ} (f : Fin m ↪o Fin n)
    (t : OrderedTriple m) :
    (P.restrict f).tripleColoring t = P.tripleColoring.restrict f t :=
  rfl

theorem restrict_tripleColoring {m : ℕ} (f : Fin m ↪o Fin n) :
    (P.restrict f).tripleColoring = P.tripleColoring.restrict f := by
  funext t
  rfl

@[simp] theorem turn_eq_left_iff (i j k : Fin n) :
    P.turn i j k = Turn.left ↔
      0 < orientation (P.point i) (P.point j) (P.point k) := by
  simp [turn]

/-- The slope of the directed segment from `a` to `b`, in the coordinates
fixed by the sweep. -/
def slope (a b : Point 2) : ℝ :=
  (b 1 - a 1) / (b 0 - a 0)

theorem orientation_eq_sweep_differences_mul_slope_sub
    (a b c : Point 2) (hab : b 0 ≠ a 0) (hbc : c 0 ≠ b 0) :
    orientation a b c =
      (b 0 - a 0) * (c 0 - b 0) * (slope b c - slope a b) := by
  simp only [slope, orientation]
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hbc]
  ring

/-- This is the formal version of the user's angle convention: for points in
sweep order, a left turn is exactly an increase in consecutive slopes. -/
theorem turn_eq_left_iff_slope_lt (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    P.turn i j k = Turn.left ↔
      slope (P.point i) (P.point j) < slope (P.point j) (P.point k) := by
  rw [P.turn_eq_left_iff]
  have hxij : P.point i 0 < P.point j 0 := P.sweep_strictMono hij
  have hxjk : P.point j 0 < P.point k 0 := P.sweep_strictMono hjk
  rw [orientation_eq_sweep_differences_mul_slope_sub _ _ _
    (ne_of_gt hxij) (ne_of_gt hxjk)]
  have hdxij : 0 < P.point j 0 - P.point i 0 := sub_pos.mpr hxij
  have hdxjk : 0 < P.point k 0 - P.point j 0 := sub_pos.mpr hxjk
  constructor <;> intro h
  · rcases (mul_pos_iff.mp h) with hpositive | hnegative
    · exact sub_pos.mp hpositive.2
    · have hproduct : 0 <
          (P.point j 0 - P.point i 0) * (P.point k 0 - P.point j 0) :=
        mul_pos hdxij hdxjk
      exact (not_lt_of_ge hproduct.le hnegative.1).elim
  · have : 0 < slope (P.point j) (P.point k) - slope (P.point i) (P.point j) :=
      sub_pos.mpr h
    exact mul_pos (mul_pos hdxij hdxjk) this

/-- For increasing indices, the other turn is genuinely a negative
orientation rather than a degenerate triple. -/
theorem turn_eq_right_iff (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    P.turn i j k = Turn.right ↔
      orientation (P.point i) (P.point j) (P.point k) < 0 := by
  have hij_ne : i ≠ j := ne_of_lt hij
  have hjk_ne : j ≠ k := ne_of_lt hjk
  have hik_ne : i ≠ k := ne_of_lt (hij.trans hjk)
  have hne := P.generalPosition hij_ne hik_ne hjk_ne
  constructor
  · intro hturn
    have hnpos : ¬0 < orientation (P.point i) (P.point j) (P.point k) := by
      intro hpos
      simp [turn, hpos] at hturn
    exact lt_of_le_of_ne (le_of_not_gt hnpos) hne
  · intro hneg
    have hnpos : ¬0 < orientation (P.point i) (P.point j) (P.point k) :=
      not_lt.mpr hneg.le
    simp [turn, hnpos]

/-- A right turn is exactly a decrease in consecutive slopes. -/
theorem turn_eq_right_iff_slope_gt (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    P.turn i j k = Turn.right ↔
      slope (P.point j) (P.point k) < slope (P.point i) (P.point j) := by
  rw [P.turn_eq_right_iff i j k hij hjk]
  have hxij : P.point i 0 < P.point j 0 := P.sweep_strictMono hij
  have hxjk : P.point j 0 < P.point k 0 := P.sweep_strictMono hjk
  rw [orientation_eq_sweep_differences_mul_slope_sub _ _ _
    (ne_of_gt hxij) (ne_of_gt hxjk)]
  have hdxij : 0 < P.point j 0 - P.point i 0 := sub_pos.mpr hxij
  have hdxjk : 0 < P.point k 0 - P.point j 0 := sub_pos.mpr hxjk
  constructor <;> intro h
  · rcases (mul_neg_iff.mp h) with hpositive | hnegative
    · exact sub_neg.mp hpositive.2
    · have hproduct : 0 <
          (P.point j 0 - P.point i 0) * (P.point k 0 - P.point j 0) :=
        mul_pos hdxij hdxjk
      exact (not_lt_of_ge hproduct.le hnegative.1).elim
  · exact mul_neg_of_pos_of_neg (mul_pos hdxij hdxjk) (sub_neg.mpr h)

/-- The ordered triple coloring induced by a sweep labels a triple left exactly
when its consecutive slopes increase. -/
theorem tripleColoring_eq_left_iff_slope_lt (t : OrderedTriple n) :
    P.tripleColoring t = Turn.left ↔
      slope (P.point t.i) (P.point t.j) < slope (P.point t.j) (P.point t.k) :=
  P.turn_eq_left_iff_slope_lt t.i t.j t.k t.hij t.hjk

end SweptConfiguration

/-- A triple coloring is sweep-realizable when it is induced by an actual
planar configuration in general position.  Theorems that are not valid for
arbitrary colorings must carry this predicate or retain the configuration. -/
def IsSweepRealizable {n : ℕ} (χ : TripleColoring n) : Prop :=
  ∃ P : SweptConfiguration n, P.tripleColoring = χ

theorem SweptConfiguration.tripleColoring_isSweepRealizable {n : ℕ}
    (P : SweptConfiguration n) : IsSweepRealizable P.tripleColoring := by
  exact ⟨P, rfl⟩

/-- Increasing restrictions of sweep-realizable colorings remain
sweep-realizable. -/
theorem IsSweepRealizable.restrict {m n : ℕ} {χ : TripleColoring n}
    (hχ : IsSweepRealizable χ) (f : Fin m ↪o Fin n) :
    IsSweepRealizable (χ.restrict f) := by
  obtain ⟨P, rfl⟩ := hχ
  exact ⟨P.restrict f, P.restrict_tripleColoring f⟩

/-- An increasing `k`-term sequence whose every triple has color `c`.  This is
the common combinatorial core of cups (`left`) and caps (`right`). -/
def IsMonochromaticChain {n k : ℕ} (χ : TripleColoring n) (c : Turn)
    (f : Fin k → Fin n) : Prop :=
  ∃ hf : StrictMono f,
    ∀ ⦃i j l : Fin k⦄, (hij : i < j) → (hjl : j < l) →
      χ ⟨f i, f j, f l, hf hij, hf hjl⟩ = c

/-- A cup in the sweep coloring. -/
abbrev IsCup {n k : ℕ} (χ : TripleColoring n) (f : Fin k → Fin n) : Prop :=
  IsMonochromaticChain χ Turn.left f

/-- A cap in the sweep coloring. -/
abbrev IsCap {n k : ℕ} (χ : TripleColoring n) (f : Fin k → Fin n) : Prop :=
  IsMonochromaticChain χ Turn.right f

/-- Passing to an increasing subsequence preserves a monochromatic chain. -/
theorem IsMonochromaticChain.comp {n k l : ℕ} {χ : TripleColoring n}
    {c : Turn} {f : Fin k → Fin n} (h : IsMonochromaticChain χ c f)
    (e : Fin l ↪o Fin k) : IsMonochromaticChain χ c (f ∘ e) := by
  rcases h with ⟨hf, hall⟩
  refine ⟨hf.comp e.strictMono, ?_⟩
  intro i j r hij hjr
  exact hall (e.strictMono hij) (e.strictMono hjr)

/-- A monochromatic chain in a restricted coloring maps to one in the
ambient coloring. -/
theorem IsMonochromaticChain.map_of_restrict_eq {n m k : ℕ}
    {χ : TripleColoring n} {ψ : TripleColoring m} {c : Turn}
    (e : Fin m ↪o Fin n) (hrestrict : χ.restrict e = ψ)
    {f : Fin k → Fin m} (h : IsMonochromaticChain ψ c f) :
    IsMonochromaticChain χ c (e ∘ f) := by
  rcases h with ⟨hf, hall⟩
  refine ⟨e.strictMono.comp hf, ?_⟩
  intro i j r hij hjr
  have hcolor := hall hij hjr
  have heq := congrFun hrestrict ⟨f i, f j, f r, hf hij, hf hjr⟩
  exact heq.trans hcolor

/-- Conversely, a chain whose vertices factor through an increasing
restriction is a chain in that restricted coloring. -/
theorem IsMonochromaticChain.of_comp_of_restrict_eq {n m k : ℕ}
    {χ : TripleColoring n} {ψ : TripleColoring m} {c : Turn}
    (e : Fin m ↪o Fin n) (hrestrict : χ.restrict e = ψ)
    {f : Fin k → Fin m} (h : IsMonochromaticChain χ c (e ∘ f)) :
    IsMonochromaticChain ψ c f := by
  rcases h with ⟨hef, hall⟩
  have hf : StrictMono f := by
    intro i j hij
    exact e.lt_iff_lt.mp (hef hij)
  refine ⟨hf, ?_⟩
  intro i j r hij hjr
  have hcolor := hall hij hjr
  have heq := congrFun hrestrict ⟨f i, f j, f r, hf hij, hf hjr⟩
  exact heq.symm.trans hcolor

end

end ErdosSzekeres

end
