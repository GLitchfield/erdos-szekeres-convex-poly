module

public import ErdosSzekeres.Chains
public import ErdosSzekeres.StrongPolygon
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-!
# The cup--cap recurrence and classical upper bound

This file formalizes the pigeonhole recurrence behind the Erdős--Szekeres
cup--cap theorem, converts the resulting consecutive chains to all-triples
chains in realizable sweep colorings, and derives the classical binomial upper
bound for convex polygons.

The recurrence proof structure is adapted and substantially rewritten from
Jineon Baek's Apache-2.0 Lean formalization, `jcpaik/erdos-tuza-valtr`, at
commit `a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f`.  In particular, this version
uses this project's `Turn`, `SweptConfiguration`, and public convex-subset API.
See `NOTICE` for attribution and license information.
-/

namespace ErdosSzekeres
namespace CupCap

variable {α : Type*} [LinearOrder α]

inductive Consecutive (R : α → α → α → Prop) : α → α → List α → Prop
  | nil {a b : α} : Consecutive R a b []
  | cons {a b c : α} {l : List α} :
      R a b c → Consecutive R b c l → Consecutive R a b (c :: l)

def Consecutive' (R : α → α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => Consecutive R a b l

omit [LinearOrder α] in
@[simp] theorem consecutive_cons {R : α → α → α → Prop}
    {a b c : α} {l : List α} :
    Consecutive R a b (c :: l) ↔ R a b c ∧ Consecutive R b c l := by
  constructor
  · intro h
    cases h with
    | cons hr ht => exact ⟨hr, ht⟩
  · rintro ⟨hr, ht⟩
    exact ht.cons hr

omit [LinearOrder α] in
@[simp] theorem consecutive_nil {R : α → α → α → Prop} {a b : α} :
    Consecutive R a b [] := Consecutive.nil

omit [LinearOrder α] in
theorem consecutive'_getElem {R : α → α → α → Prop}
    {l : List α} (h : Consecutive' R l) (i : ℕ) (hi : i + 2 < l.length) :
    R l[i] l[i + 1] l[i + 2] := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons a l =>
          cases l with
          | nil => simp at hi
          | cons b l =>
              cases l with
              | nil => simp at hi
              | cons c l =>
                  exact (consecutive_cons.mp h).1
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons a l =>
          have htail : Consecutive' R l := by
            cases l with
            | nil => simp [Consecutive']
            | cons b l =>
                cases l with
                | nil => simp [Consecutive']
                | cons c l => exact (consecutive_cons.mp h).2
          have hi' : i + 2 < l.length := by simp at hi; omega
          simpa using ih htail hi'

def IsTurnChain (κ : α → α → α → Turn) (c : Turn) (l : List α) : Prop :=
  l.IsChain (fun a b => a < b) ∧ Consecutive' (fun a b d => κ a b d = c) l

@[simp] theorem isTurnChain_nil (κ : α → α → α → Turn) (c : Turn) :
    IsTurnChain κ c [] := by simp [IsTurnChain, Consecutive']

@[simp] theorem isTurnChain_singleton (κ : α → α → α → Turn)
    (c : Turn) (a : α) : IsTurnChain κ c [a] := by
  simp [IsTurnChain, Consecutive']

@[simp] theorem isTurnChain_pair {κ : α → α → α → Turn}
    {c : Turn} {a b : α} : IsTurnChain κ c [a, b] ↔ a < b := by
  simp [IsTurnChain, Consecutive']

@[simp] theorem isTurnChain_cons3 {κ : α → α → α → Turn}
    {t : Turn} {a b c : α} {l : List α} :
    IsTurnChain κ t (a :: b :: c :: l) ↔
      a < b ∧ κ a b c = t ∧ IsTurnChain κ t (b :: c :: l) := by
  simp [IsTurnChain, Consecutive', and_left_comm, and_assoc]

@[simp] theorem isTurnChain_append_cons3 {κ : α → α → α → Turn}
    {t : Turn} {a b c : α} {l₁ l₂ : List α} :
    IsTurnChain κ t (l₁ ++ a :: b :: c :: l₂) ↔
      IsTurnChain κ t (l₁ ++ [a, b]) ∧ κ a b c = t ∧
        IsTurnChain κ t (b :: c :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons d l₁ ih =>
      cases l₁ with
      | nil => simp [and_assoc]
      | cons e l₁ =>
          cases l₁ with
          | nil => simp [and_assoc]
          | cons f l₁ =>
              simp only [List.cons_append, isTurnChain_cons3]
              simp only [List.cons_append] at ih
              rw [ih]
              aesop

def ListIn (l : List α) (S : Finset α) : Prop :=
  ∀ x, x ∈ l → x ∈ S

def HasNChain (κ : α → α → α → Turn) (c : Turn)
    (k : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, IsTurnChain κ c l ∧ l.length = k ∧ ListIn l S

theorem has_chain_two (κ : α → α → α → Turn) (c : Turn)
    {S : Finset α} (hS : 1 < S.card) : HasNChain κ c 2 S := by
  have hcard : 2 ≤ S.card := by omega
  let f : Fin 2 ↪o α := S.orderEmbOfCardLe hcard
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  refine ⟨[f 0, f 1], ?_, by simp, ?_⟩
  · simp [h01]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact Finset.orderEmbOfCardLe_mem S hcard _

omit [LinearOrder α] in
@[simp] theorem listIn_cons {a : α} {l : List α} {S : Finset α} :
    ListIn (a :: l) S ↔ a ∈ S ∧ ListIn l S := by
  simp [ListIn]

omit [LinearOrder α] in
@[simp] theorem listIn_append {l₁ l₂ : List α} {S : Finset α} :
    ListIn (l₁ ++ l₂) S ↔ ListIn l₁ S ∧ ListIn l₂ S := by
  simp [ListIn, or_imp, forall_and]

private def takeHead2 : ∀ {l : List α}, 2 ≤ l.length →
    Σ' (a b : α) (t : List α), l = a :: b :: t
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: b :: t, _ => ⟨a, b, t, rfl⟩

private def takeLast2 : ∀ {l : List α}, 2 ≤ l.length →
    Σ' (a b : α) (t : List α), l = t ++ [a, b]
  | [], h => by simp at h
  | [_], h => by simp at h
  | [a, b], _ => ⟨a, b, [], rfl⟩
  | a :: b :: c :: t, _ =>
      let ⟨x, y, u, hu⟩ := takeLast2 (l := b :: c :: t) (by simp)
      ⟨x, y, a :: u, congrArg (List.cons a) hu⟩

theorem hasNChain_mono {c : Turn} {m : ℕ} {S T : Finset α}
    {κ : α → α → α → Turn} (hST : S ⊆ T) :
    HasNChain κ c m S → HasNChain κ c m T := by
  rintro ⟨l, hchain, hlen, hin⟩
  exact ⟨l, hchain, hlen, fun x hx => hST (hin x hx)⟩

theorem cup_cap (κ : α → α → α → Turn) (a b : ℕ)
    (S : Finset α) (hS : Nat.choose (a + b) a < S.card) :
    HasNChain κ Turn.right (a + 2) S ∨
      HasNChain κ Turn.left (b + 2) S := by
  classical
  revert a b S hS
  refine Nat.pincerRecursion ?_ ?_ ?_
  · intro a S hS
    right
    apply has_chain_two κ Turn.left
    simpa using hS
  · intro b S hS
    left
    apply has_chain_two κ Turn.right
    simpa using hS
  · intro a b hab ha S hS
    have hchoose : Nat.choose (a + 1 + (b + 1)) (a + 1) =
        Nat.choose (a + (b + 1)) a + Nat.choose (a + 1 + b) (a + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.choose_succ_succ' (a + b + 1) a
    let startsCap : α → Prop := fun p =>
      ∃ l : List α, IsTurnChain κ Turn.right l ∧ ListIn l S ∧
        l.length = a + 2 ∧ p ∈ l.head?
    let T := S.filter startsCap
    have hTS : T ⊆ S := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    have hcard : (S \ T).card + T.card = S.card := by
      exact Finset.card_sdiff_add_card_eq_card hTS
    have hcases : Nat.choose (a + (b + 1)) a < (S \ T).card ∨
        Nat.choose (a + 1 + b) (a + 1) < T.card := by
      rw [hchoose] at hS
      omega
    rcases hcases with hlarge | hlarge
    · rcases hab (S \ T) hlarge with hcap | hcup
      · obtain ⟨l, hlchain, hllen, hlin⟩ := hcap
        have hl2 : 2 ≤ l.length := by omega
        obtain ⟨p, q, rest, rfl⟩ := takeHead2 hl2
        have hp_not : p ∉ T := (Finset.mem_sdiff.mp (hlin p (by simp))).2
        apply False.elim
        apply hp_not
        change p ∈ S.filter startsCap
        apply Finset.mem_filter.mpr
        refine ⟨(Finset.mem_sdiff.mp (hlin p (by simp))).1, ?_⟩
        exact ⟨p :: q :: rest, hlchain,
          fun x hx => (Finset.mem_sdiff.mp (hlin x hx)).1, hllen, by simp⟩
      · right
        exact hasNChain_mono (Finset.sdiff_subset) hcup
    · rcases ha T hlarge with hcap | hcup
      · left
        exact hasNChain_mono hTS hcap
      · obtain ⟨l, hlchain, hllen, hlin⟩ := hcup
        have hl2 : 2 ≤ l.length := by omega
        obtain ⟨p, q, pre, hl⟩ := takeLast2 hl2
        have hqT : q ∈ T := hlin q (by rw [hl]; simp)
        have hqStart := (Finset.mem_filter.mp hqT).2
        obtain ⟨rchain, hrchain, hrin, hrlen, hqhead⟩ := hqStart
        have hr2 : 2 ≤ rchain.length := by omega
        obtain ⟨q', r, suffix, hr⟩ := takeHead2 hr2
        rw [hr] at hqhead
        simp at hqhead
        subst q'
        by_cases hpqr : κ p q r = Turn.left
        · right
          refine ⟨l ++ [r], ?_, ?_, ?_⟩
          · rw [hl]
            rw [hr] at hrchain
            rw [List.append_assoc]
            change IsTurnChain κ Turn.left (pre ++ p :: q :: r :: [])
            rw [isTurnChain_append_cons3]
            refine ⟨by simpa [hl] using hlchain, hpqr, ?_⟩
            apply isTurnChain_pair.mpr
            exact (List.isChain_cons_cons.mp hrchain.1).1
          · simp [hllen]
          · rw [listIn_append]
            refine ⟨fun x hx => (Finset.mem_filter.mp (hlin x hx)).1, ?_⟩
            intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            subst x
            exact hrin r (by rw [hr]; simp)
        · left
          have hpqr' : κ p q r = Turn.right := by
            cases h : κ p q r <;> simp_all
          refine ⟨p :: rchain, ?_, ?_, ?_⟩
          · rw [hr]
            rw [hr] at hrchain
            rw [hl] at hlchain
            rw [isTurnChain_cons3]
            refine ⟨?_, hpqr', hrchain⟩
            have hpq : p < q := by
              have hs := hlchain.1
              exact (List.isChain_append_cons_cons.mp hs).2.1
            exact hpq
          · simp [hrlen]
          · rw [listIn_cons]
            refine ⟨?_, hrin⟩
            exact (Finset.mem_filter.mp (hlin p (by rw [hl]; simp))).1

def totalColor {n : ℕ} (χ : TripleColoring n) (i j k : Fin n) : Turn :=
  if hij : i < j then
    if hjk : j < k then χ ⟨i, j, k, hij, hjk⟩ else Turn.left
  else Turn.left

theorem totalColor_of_lt {n : ℕ} (χ : TripleColoring n)
    {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    totalColor χ i j k = χ ⟨i, j, k, hij, hjk⟩ := by
  simp [totalColor, hij, hjk]

def HasMonochromaticChain {n : ℕ} (χ : TripleColoring n) (c : Turn)
    (k : ℕ) : Prop :=
  ∃ f : Fin k ↪o Fin n, IsMonochromaticChain χ c f

abbrev HasCup {n : ℕ} (χ : TripleColoring n) (k : ℕ) : Prop :=
  HasMonochromaticChain χ Turn.left k

abbrev HasCap {n : ℕ} (χ : TripleColoring n) (k : ℕ) : Prop :=
  HasMonochromaticChain χ Turn.right k

theorem SweptConfiguration.hasMonochromaticChain_of_hasNChain
    {n m : ℕ} (P : SweptConfiguration n) (c : Turn)
    (h : HasNChain (totalColor P.tripleColoring) c m Finset.univ) :
    HasMonochromaticChain P.tripleColoring c m := by
  obtain ⟨l, hchain, hlen, _⟩ := h
  subst m
  let f : Fin l.length ↪o Fin n :=
    OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
  refine ⟨f, ?_⟩
  apply (ErdosSzekeres.SweptConfiguration.isMonochromaticChain_iff_isConsecutiveMonochromaticChain
    P c f).mpr
  refine ⟨f.strictMono, ?_⟩
  intro i j k hij hjk hij_succ hjk_succ
  have hi : i.val + 2 < l.length := by
    omega
  have hturn := consecutive'_getElem hchain.2 i.val hi
  have hfij : f i < f j := f.strictMono hij
  have hfjk : f j < f k := f.strictMono hjk
  have hturn' : totalColor P.tripleColoring (f i) (f j) (f k) = c := by
    simpa [f, hij_succ, hjk_succ] using hturn
  rw [totalColor_of_lt P.tripleColoring hfij hfjk] at hturn'
  exact hturn'

theorem SweptConfiguration.hasCap_or_hasCup_choose
    {n : ℕ} (P : SweptConfiguration n) (a b : ℕ)
    (hn : Nat.choose (a + b) a < n) :
    HasCap P.tripleColoring (a + 2) ∨ HasCup P.tripleColoring (b + 2) := by
  have h := cup_cap (totalColor P.tripleColoring) a b Finset.univ (by simpa using hn)
  rcases h with hcap | hcup
  · exact Or.inl
      (SweptConfiguration.hasMonochromaticChain_of_hasNChain P Turn.right hcap)
  · exact Or.inr
      (SweptConfiguration.hasMonochromaticChain_of_hasNChain P Turn.left hcup)

/-- A monochromatic cup or cap satisfies the strong-polygon law. -/
theorem IsMonochromaticChain.isStrongPolygonOn
    {n k : ℕ} {χ : TripleColoring n} {c : Turn} {f : Fin k ↪o Fin n}
    (h : IsMonochromaticChain χ c f) : IsStrongPolygonOn χ f := by
  rcases h with ⟨_, hall⟩
  intro i j l r hij hjl hlr
  constructor
  · exact (hall hij hjl).trans (hall hij (hjl.trans hlr)).symm
  · exact (hall (hij.trans hjl) hlr).trans (hall hjl hlr).symm

/-- Standard-parameter upper half of the exact cup--cap theorem. -/
theorem SweptConfiguration.hasCap_or_hasCup
    {n a b : ℕ} (P : SweptConfiguration n) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hn : Nat.choose (a + b - 4) (a - 2) < n) :
    HasCap P.tripleColoring a ∨ HasCup P.tripleColoring b := by
  have hab : (a - 2) + (b - 2) = a + b - 4 := by omega
  have ha' : (a - 2) + 2 = a := by omega
  have hb' : (b - 2) + 2 = b := by omega
  have hchoose : Nat.choose ((a - 2) + (b - 2)) (a - 2) < n := by
    rwa [hab]
  simpa [ha', hb'] using
    (SweptConfiguration.hasCap_or_hasCup_choose P (a - 2) (b - 2) hchoose)

/-- The cup--cap threshold forces a convex subset in every presented planar
configuration. -/
theorem SweptPresentation.containsConvexSubset_of_cupCap
    {s : Finset (Point 2)} (P : SweptPresentation s) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) + 1 ≤ s.card) :
    ContainsConvexSubset s a ∨ ContainsConvexSubset s b := by
  have hlt : Nat.choose (a + b - 4) (a - 2) < s.card := by omega
  rcases SweptConfiguration.hasCap_or_hasCup P.configuration ha hb hlt with
    ⟨f, hf⟩ | ⟨f, hf⟩
  · left
    exact (P.containsConvexSubset_iff_exists_isStrongPolygonOn a).2
      ⟨f, IsMonochromaticChain.isStrongPolygonOn hf⟩
  · right
    exact (P.containsConvexSubset_iff_exists_isStrongPolygonOn b).2
      ⟨f, IsMonochromaticChain.isStrongPolygonOn hf⟩

/-- The classical Erdős--Szekeres binomial upper bound. -/
theorem classical_binomial_upper (k : ℕ) (hk : 3 ≤ k) :
    ForcesConvexPolygon k (Nat.choose (2 * k - 4) (k - 2) + 1) := by
  intro s hcard hgp
  let P := Classical.choice (exists_sweptPresentation s hgp)
  have hsum : k + k - 4 = 2 * k - 4 := by omega
  have hcard' : Nat.choose (k + k - 4) (k - 2) + 1 ≤ s.card := by
    rwa [hsum]
  rcases SweptPresentation.containsConvexSubset_of_cupCap
      P k k (by omega) (by omega) hcard' with
    h | h
  · exact h
  · exact h

end CupCap
end ErdosSzekeres

end
