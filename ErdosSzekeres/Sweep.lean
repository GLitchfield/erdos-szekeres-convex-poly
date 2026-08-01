import ErdosSzekeres.Basic

/-!
# Sweeps and the left/right triple coloring

We normalize the user's generic sweep direction to the first coordinate.  A
future affine-invariance layer will justify this normalization for an arbitrary
line.  The mathematical content below is already coordinate-independent at the
level of the orientation sign.
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

end

end ErdosSzekeres
