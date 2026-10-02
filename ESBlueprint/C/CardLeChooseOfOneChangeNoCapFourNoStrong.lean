import ErdosSzekeres.StructuralChargingCore
/- J. Baek's Apache-2.0 ETV development, ported for R21. -/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Lib/Core/Rel3.lean.
Modified for Lean 4.29.1; scoped within this node. -/
section
open List

universe u v

open OrderDual

def BaekMirror2 {α : Type u} [LinearOrder α] {β : Sort v} (f : α → α → β) : αᵒᵈ → αᵒᵈ → β := fun a b =>
  f (ofDual b) (ofDual a)

def BaekMirror3 {α : Type u} [LinearOrder α] {β : Sort v} (f : α → α → α → β) : αᵒᵈ → αᵒᵈ → αᵒᵈ → β :=
  fun a b c => f (ofDual c) (ofDual b) (ofDual a)

@[reducible]
def BaekDecidableRel3 {α : Sort u} (r : α → α → α → Prop) :=
  ∀ a b c : α, Decidable (r a b c)

@[reducible]
def DecidableRel.BaekMirror2 {α : Type u} [LinearOrder α] {r : α → α → Prop} (dec : DecidableRel r) :
    DecidableRel (BaekMirror2 r) := fun a b => dec (ofDual b) (ofDual a)

@[reducible]
def BaekDecidableRel3.BaekMirror3 {α : Type u} [LinearOrder α] {r : α → α → α → Prop}
    (dec : BaekDecidableRel3 r) : BaekDecidableRel3 (BaekMirror3 r) := fun a b c =>
  dec (ofDual c) (ofDual b) (ofDual a)

end

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Lib/List/Defs.lean.
Modified for Lean 4.29.1; scoped within this node. -/
section
open List

variable {α : Type _}

-- Local notion for a list contained in a finset
protected def List.baekIn (l : List α) (S : Finset α) : Prop :=
  ∀ a : α, a ∈ l → a ∈ S

protected def Finset.BaekMirror [LinearOrder α] (S : Finset α) : Finset αᵒᵈ :=
  Finset.image OrderDual.toDual S

protected def Finset.ofBaekMirror [LinearOrder α] (S : Finset αᵒᵈ) : Finset α :=
  Finset.image OrderDual.ofDual S

namespace List

-- Local notion for flipping a list of elements, together with its order
protected def BaekMirror [LinearOrder α] (l : List α) : List αᵒᵈ :=
  (List.map OrderDual.toDual l).reverse

protected def ofBaekMirror [LinearOrder α] (l : List αᵒᵈ) : List α :=
  (List.map OrderDual.ofDual l).reverse

variable (R : α → α → α → Prop)

inductive BaekChain3 : α → α → List α → Prop
  | nil {a b : α} : BaekChain3 a b []
  | cons : ∀ {a b c : α} {l : List α}, R a b c → BaekChain3 b c l → BaekChain3 a b (c :: l)

def BaekChain3' : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => BaekChain3 R a b l

variable {R}

@[simp]
theorem chain3_cons {a b c : α} {l : List α} : BaekChain3 R a b (c :: l) ↔ R a b c ∧ BaekChain3 R b c l :=
  ⟨fun p => by cases' p with _ a b c l _ n p <;> exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩

@[simp]
theorem chain3_nil {a b : α} : BaekChain3 R a b [] := BaekChain3.nil

instance decidableChain3 [BaekDecidableRel3 R] (a b : α) (l : List α) : Decidable (BaekChain3 R a b l) := by
  induction l generalizing a b <;> simp only [BaekChain3.nil, chain3_cons] <;> infer_instance

instance decidableChain3' [BaekDecidableRel3 R] (l : List α) : Decidable (BaekChain3' R l) := by
  cases' l with _ l <;> try cases' l with _ l <;> dsimp only [BaekChain3'] <;> infer_instance
  rw [BaekChain3']
  infer_instance

end List

end

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Lib/List/Chain3.lean.
Modified for Lean 4.29.1; scoped within this node. -/
section
open List

variable {α : Type _} {R : α → α → α → Prop}

namespace List

theorem chain3_split {a b c d : α} {l1 l2 : List α} :
    BaekChain3 R a b (l1 ++ c :: d :: l2) ↔ BaekChain3 R a b (l1 ++ [c, d]) ∧ BaekChain3 R c d l2 := by
  induction' l1 with x l1 IH generalizing a b
  · simp only [nil_append, chain3_cons, BaekChain3, BaekChain3.nil, and_true, and_assoc]
  · simp only [cons_append, chain3_cons, IH, and_assoc]

@[simp]
theorem chain3_append_cons3 {a b c d e : α} {l1 l2 : List α} :
    BaekChain3 R a b (l1 ++ c :: d :: e :: l2) ↔
      BaekChain3 R a b (l1 ++ [c, d]) ∧ R c d e ∧ BaekChain3 R d e l2 :=
  by rw [chain3_split, chain3_cons]

@[simp]
theorem chain3'_nil : BaekChain3' R [] :=
  trivial

@[simp]
theorem chain3'_singleton (a : α) : BaekChain3' R [a] :=
  trivial

@[simp]
theorem chain3'_pair (a b : α) : BaekChain3' R [a, b] :=
  BaekChain3.nil

@[simp]
theorem chain3'_cons {x y z l} : BaekChain3' R (x :: y :: z :: l) ↔ R x y z ∧ BaekChain3' R (y :: z :: l) :=
  chain3_cons

theorem chain3'_split {a b : α} :
    ∀ {l1 l2 : List α},
      BaekChain3' R (l1 ++ a :: b :: l2) ↔ BaekChain3' R (l1 ++ [a, b]) ∧ BaekChain3' R (a :: b :: l2)
  | [], l2 => (and_iff_right (chain3'_pair a b)).symm
  | [c], l2 => by simp
  |-- todo
      c ::
      d :: l1,
    l2 => chain3_split

@[simp]
theorem chain3'_append_cons3 {a b c : α} {l1 l2 : List α} :
    BaekChain3' R (l1 ++ a :: b :: c :: l2) ↔
      BaekChain3' R (l1 ++ [a, b]) ∧ R a b c ∧ BaekChain3' R (b :: c :: l2) :=
  by rw [chain3'_split, chain3'_cons]

theorem BaekChain3'.left_of_append {l1 l2 : List α} (h : BaekChain3' R (l1 ++ l2)) : BaekChain3' R l1 :=
  by
  induction' l1 with a l1 ih; simp
  cases' l1 with b l1; simp
  cases' l1 with c l1; simp
  simp at h ⊢; tauto

theorem BaekChain3'.right_of_append {l1 l2 : List α} (h : BaekChain3' R (l1 ++ l2)) : BaekChain3' R l2 :=
  by
  revert l2
  induction' l1 with a l1 ih; intro l2 h'; exact h'
  intro l2 h'
  cases' l1 with b l1
  · cases' l2 with c l2; simp
    cases' l2 with d l2; simp
    simp at h'; exact h'.right
  cases' l1 with c l1
  · cases' l2 with d l2; simp
    cases' l2 with e l2; simp
    simp at h'; exact h'.right.right
  apply ih; simp at h' ⊢; exact h'.right

theorem BaekChain3'.infix {l₁ l : List α} (h : BaekChain3' R l) (h' : l₁ <:+: l) : BaekChain3' R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩; exact h.left_of_append.right_of_append

theorem BaekChain3'.suffix {l₁ l : List α} (h : BaekChain3' R l) (h' : l₁ <:+ l) : BaekChain3' R l₁ :=
  h.infix h'.isInfix

theorem BaekChain3'.prefix {l₁ l : List α} (h : BaekChain3' R l) (h' : l₁ <+: l) : BaekChain3' R l₁ :=
  h.infix h'.isInfix

theorem BaekChain3'.drop {l : List α} (h : BaekChain3' R l) (n : ℕ) : BaekChain3' R (drop n l) :=
  h.suffix (drop_suffix _ _)

theorem BaekChain3'.dropLast {l : List α} (h : BaekChain3' R l) : BaekChain3' R l.dropLast :=
  h.prefix l.dropLast_prefix

theorem BaekChain3'.take {l : List α} (h : BaekChain3' R l) (n : ℕ) : BaekChain3' R (take n l) :=
  h.prefix (take_prefix _ _)

theorem BaekChain3'.tail {l : List α} (h : BaekChain3' R l) : BaekChain3' R l.tail :=
  by
  cases' l with a l; simp
  cases' l with b l; simp
  cases' l with c l; simp
  simp at h ⊢; exact h.right

theorem chain3'_mirror [LinearOrder α] {l : List α} : BaekChain3' (BaekMirror3 R) l.BaekMirror ↔ BaekChain3' R l :=
  by
  induction' l with a l ih; simp only [List.BaekMirror, map_nil, reverse_nil, chain3'_nil]
  cases' l with b l; simp only [List.BaekMirror, map_cons, map_nil, reverse_cons, reverse_nil,
    nil_append, chain3'_singleton]
  cases' l with c l
  rw [List.BaekMirror]; simp
  rw [List.BaekMirror]; simp
  simp [List.BaekMirror] at ih; rw [← ih]
  rw [BaekMirror3]; simp; exact and_comm

end List

end

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Lib/List/Lemmas.lean.
Modified for Lean 4.29.1; scoped within this node. -/
section
open List

variable {α : Type _}

section ListIn

def List.baek_in_superset {l : List α} {S T : Finset α} (h : S ⊆ T) : l.baekIn S → l.baekIn T :=
  fun l_in_S a al => h (l_in_S _ al)

def List.baek_subset_in {l1 l2 : List α} {S : Finset α} (h : l1 ⊆ l2) (h_l2 : l2.baekIn S) : l1.baekIn S :=
  fun a ha => h_l2 a (h ha)

@[simp]
theorem List.baek_nil_in {S : Finset α} : [].baekIn S := by rw [List.baekIn] <;> simp

@[simp]
theorem List.baek_cons_in {a : α} {l : List α} {S : Finset α} : (a :: l).baekIn S ↔ a ∈ S ∧ l.baekIn S := by
  simp [List.baekIn]

@[simp]
theorem List.baek_append_in {l1 l2 : List α} {S : Finset α} : (l1 ++ l2).baekIn S ↔ l1.baekIn S ∧ l2.baekIn S :=
  by
  constructor
  · intro h; constructor
    intro a al1; apply h; exact List.mem_append_left l2 al1
    intro a al2; apply h; exact List.mem_append_right l1 al2
  · intro h a al12; cases' h with h1 h2
    simp at al12; cases' al12 with al1 al2
    exact h1 _ al1; exact h2 _ al2

@[simp]
theorem List.baek_reverse_in {l : List α} {S : Finset α} : l.reverse.baekIn S ↔ l.baekIn S := by simp [List.baekIn]

end ListIn

@[simp]
theorem List.baek_reverse_getLast? {l : List α} : l.reverse.getLast? = l.head? := by cases l <;> simp

@[simp]
theorem List.baek_reverse_head? {l : List α} : l.reverse.head? = l.getLast? := by
  convert List.baek_reverse_getLast?.symm; simp

section BaekMirror

variable [LinearOrder α]

open OrderDual

@[simp]
theorem List.BaekMirror_nil : ([] : List α).BaekMirror = [] :=
  rfl

@[simp]
theorem List.BaekMirror_singleton {a : α} : [a].BaekMirror = [toDual a] :=
  rfl

@[simp]
theorem List.BaekMirror_cons {a : α} {l : List α} : (a :: l).BaekMirror = l.BaekMirror ++ [toDual a] := by
  simp [List.BaekMirror]

@[simp]
theorem List.BaekMirror_append {l1 l2 : List α} : (l1 ++ l2).BaekMirror = l2.BaekMirror ++ l1.BaekMirror := by
  simp [List.BaekMirror]

@[simp]
theorem List.ofBaekMirror_nil : ([] : List αᵒᵈ).ofBaekMirror = [] :=
  rfl

@[simp]
theorem List.ofBaekMirrorBaekMirror {l : List αᵒᵈ} : l.ofBaekMirror.BaekMirror = l :=
  by simp [List.ofBaekMirror, List.BaekMirror]

@[simp]
theorem Finset.ofBaekMirrorBaekMirror {S : Finset αᵒᵈ} : S.ofBaekMirror.BaekMirror = S :=
  by
  rw [Finset.ofBaekMirror, Finset.BaekMirror]
  rw [Finset.image_image]; convert Finset.image_id
  infer_instance

@[simp]
theorem List.BaekMirror_length {l : List α} : l.BaekMirror.length = l.length := by rw [List.BaekMirror]; simp

theorem List.isChain_mirror {l : List α} : List.IsChain (· < ·) l.BaekMirror ↔ List.IsChain (· < ·) l := by
  simp only [List.BaekMirror, List.isChain_reverse, List.isChain_map, toDual_lt_toDual]

theorem List.BaekMirror_getLast? {l : List α} : l.BaekMirror.getLast? = Option.map toDual l.head? := by
  simp [List.BaekMirror]

theorem List.BaekMirror_head? {l : List α} : l.BaekMirror.head? = Option.map toDual l.getLast? :=
  by
  rw [List.BaekMirror, List.baek_reverse_head?]
  -- quick-and-dirty proof
  induction' l with a l ih;
  simp
  simp; cases' l with b l; simp
  simp; simp at ih; exact ih

theorem List.ofBaekMirror_getLast? {l : List αᵒᵈ} : l.ofBaekMirror.getLast? = Option.map ofDual l.head? :=
  by rw [List.ofBaekMirror] <;> cases l <;> simp <;> tauto

theorem List.ofBaekMirror_head? {l : List αᵒᵈ} : l.ofBaekMirror.head? = Option.map ofDual l.getLast? :=
  by
  rw [List.ofBaekMirror, List.baek_reverse_head?]
  -- quick-and-dirty proof
  induction' l with a l ih;
  simp
  simp; cases' l with b l; simp
  simp; simp at ih; exact ih

theorem List.BaekMirror_mem_getLast? {a : α} {l : List α} :
    toDual a ∈ l.BaekMirror.getLast? ↔ a ∈ l.head? := by rw [List.BaekMirror] <;> cases l <;> simp

theorem List.BaekMirror_mem_head? {a : α} {l : List α} : toDual a ∈ l.BaekMirror.head? ↔ a ∈ l.getLast? :=
  by
  rw [List.BaekMirror, List.baek_reverse_head?]
  -- quick-and-dirty proof
  induction' l with a l ih;
  simp
  simp; cases' l with b l; simp
  simp; simp at ih; exact ih

@[simp]
theorem List.BaekMirror_in {l : List α} {S : Finset α} : l.BaekMirror.baekIn S.BaekMirror ↔ l.baekIn S :=
  by
  rw [List.BaekMirror]; simp; constructor
  · simp [List.baekIn, Finset.BaekMirror, HasSubset.Subset]
  · simp [List.baekIn, Finset.BaekMirror]

@[simp]
theorem Finset.memBaekMirror {a : α} {S : Finset α} : toDual a ∈ S.BaekMirror ↔ a ∈ S := by
  simp [Finset.BaekMirror]

@[simp]
theorem Finset.BaekMirror_card {S : Finset α} : S.BaekMirror.card = S.card :=
  by
  rw [Finset.BaekMirror]
  apply S.card_image_of_injective
  intro a b; simp

end BaekMirror

@[simp]
theorem List.baek_dropLast_singleton (a : α) : [a].dropLast = [] := by rw [List.dropLast]

@[simp]
theorem List.baek_getLast?_cons_append_cons (a b : α) (l1 l2 : List α) :
    (a :: (l1 ++ b :: l2)).getLast? = (b :: l2).getLast? := by
  revert a <;> induction' l1 with c l1 ih <;> simp <;> intro <;> exact ih c

def List.baek_takeHead' {a : α} : ∀ {l : List α} (h : a ∈ l.head?), Σ' t, l = a :: t
  | [], h => by simp at h <;> exfalso <;> assumption
  | b :: t, h => ⟨t, by simp at h ⊢ <;> assumption⟩

def List.baek_takeHead : ∀ {l : List α}, l ≠ [] → Σ' (h1 : α) (t : List α), l = h1 :: t
  | [], h => absurd rfl h
  | h1 :: t, _ => ⟨h1, t, rfl⟩

def List.baek_takeHead2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (h1 h2 : α) (t : List α), l = h1 :: h2 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: t, _ => ⟨a, b, t, rfl⟩

def List.baek_takeHead3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (h1 h2 h3 : α) (t : List α), l = h1 :: h2 :: h3 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: c :: t, _ => ⟨a, b, c, t, rfl⟩

def List.baek_takeLast' {a : α} : ∀ {l : List α} (h : a ∈ l.getLast?), Σ' l', l = l' ++ [a]
  | [], h => by simp at h
  | [a], h => ⟨[], by simp at h ⊢; assumption⟩
  | b :: c :: t, h =>
    let h' : a ∈ (c :: t).getLast? := by
      simp only [Option.mem_def, List.getLast?_cons_cons]; exact h
    let ⟨l'', hl''⟩ := List.baek_takeLast' h'
    ⟨b :: l'', by simp only [cons_append, cons.injEq, true_and]; exact hl''⟩

def List.baek_takeLast : ∀ {l : List α}, l ≠ [] → Σ' (e1 : α) (m : List α), l = m ++ [e1]
  | [], h => absurd rfl h
  | [a], h => ⟨a, [], rfl⟩
  | a :: b :: rest, _ =>
    let h : b :: rest ≠ [] := List.cons_ne_nil _ _
    let ⟨e1, m', eq_l'⟩ := List.baek_takeLast h
    ⟨e1, a :: m', congr_arg (List.cons a) eq_l'⟩

def List.baek_takeLast2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (e1 e2 : α) (m : List α), l = m ++ [e1, e2]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], h => ⟨a, b, [], rfl⟩
  | a :: b :: c :: t, _ =>
    let h : 2 ≤ (b :: c :: t).length := (2 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, m', eq_l'⟩ := List.baek_takeLast2 h
    ⟨e1, e2, a :: m', congr_arg (List.cons a) eq_l'⟩

def List.baek_takeLast3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (e1 e2 e3 : α) (m : List α), l = m ++ [e1, e2, e3]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [a], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], h => absurd h (Bool.of_decide_false rfl)
  | [a, b, c], h => ⟨a, b, c, [], rfl⟩
  | a :: b :: c :: d :: t, _ =>
    let h : 3 ≤ (b :: c :: d :: t).length := (3 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, e3, m', eq_l'⟩ := List.baek_takeLast3 h
    ⟨e1, e2, e3, a :: m', congr_arg (List.cons a) eq_l'⟩

end

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Config/Defs.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

structure Config (α : Type _) [LinearOrder α] where
  Cup3 : α → α → α → Prop
  DecidableCup3 : BaekDecidableRel3 Cup3
namespace Config

variable {α : Type _} [ord : LinearOrder α] (C : Config α)

attribute [instance] Config.DecidableCup3

-- Notion of 3-caps
def Cap3 (a b c : α) : Prop :=
  ¬C.Cup3 a b c

def DecidableCap3 : BaekDecidableRel3 C.Cap3 := fun a b c => @instDecidableNot _ (C.DecidableCup3 a b c)

attribute [instance] DecidableCap3

-- Notion of caps and cups
def Cap (l : List α) : Prop :=
  l.IsChain (· < ·) ∧ l.BaekChain3' C.Cap3

def Cup (l : List α) : Prop :=
  l.IsChain (· < ·) ∧ l.BaekChain3' C.Cup3

@[simp]
def Gon (l1 l2 : List α) : Prop :=
  2 ≤ l1.length ∧
    C.Cap l1 ∧ 2 ≤ l2.length ∧ C.Cup l2 ∧ l1.head? = l2.head? ∧ l1.getLast? = l2.getLast?

instance DecidableCup {l : List α} : Decidable (C.Cup l) := by rw [Cup] <;> infer_instance

def NCap (n : ℕ) (l : List α) : Prop :=
  C.Cap l ∧ l.length = n

def NCup (n : ℕ) (l : List α) : Prop :=
  C.Cup l ∧ l.length = n

def NGon (n : ℕ) (l1 l2 : List α) : Prop :=
  C.Gon l1 l2 ∧ l1.length + l2.length = n + 2

def HasNCap (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.NCap n l ∧ l.baekIn S

def HasNCup (n : ℕ) (S : Finset α) : Prop :=
  ∃ l : List α, C.NCup n l ∧ l.baekIn S

def HasNGon (n : ℕ) (S : Finset α) : Prop :=
  ∃ l1 l2 : List α, C.NGon n l1 l2 ∧ l1.baekIn S ∧ l2.baekIn S

end Config

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Config/Lemmas.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

variable {α : Type _} [LinearOrder α] {C : Config α}

namespace Config

namespace Cap

@[simp]
protected theorem nil : C.Cap [] := by rw [Config.Cap]; tauto

@[simp]
protected theorem singleton (a : α) : C.Cap [a] := by rw [Config.Cap]; simp

@[simp]
protected theorem pair {a b : α} : C.Cap [a, b] ↔ a < b := by rw [Config.Cap]; simp

@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cap (a::b::c::l) ↔ a < b ∧ C.Cap3 a b c ∧ C.Cap (b::c::l) := by
  repeat' rw [Config.Cap]; simp
  tauto

@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cap (l1 ++ a::b::c::l2) ↔ C.Cap (l1 ++ [a, b]) ∧ C.Cap3 a b c ∧ C.Cap (b::c::l2) :=
  by
  induction' l1 with d l1 l1_ih
  · simp [Config.Cap]; tauto
  cases' l1 with e l1
  · simp [Config.Cap]; tauto
  cases' l1 with f l1
  · simp [Config.Cap]; tauto
  simp; simp at l1_ih; rw [l1_ih]; tauto

protected theorem dropLast {l : List α} (h : C.Cap l) : C.Cap l.dropLast := by
  induction' l with a l
  · simp [Config.Cap]
  cases' l with b l
  · simp [Config.Cap]
  cases' l with c l
  · simp [Config.Cap, List.dropLast] at *
  cases' l with d l
  · simp [Config.Cap, List.dropLast] at *; tauto
  simp [List.dropLast] at *; tauto

protected theorem tail {l : List α} (h : C.Cap l) : C.Cap l.tail := by
  induction' l with a l
  · simp [Config.Cap]
  cases' l with b l
  · simp [Config.Cap]
  cases' l with c l
  · simp [Config.Cap] at *
  cases' l with d l
  · simp [Config.Cap] at *; tauto
  simp [List.dropLast] at *; tauto

end Cap

namespace NCap

protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.dropLast :=
  by
  cases' l with a l
  · simp [Config.NCap, Config.Cap] at h
  simp [Config.NCap] at *; cases' h with hc hl
  exact ⟨hc.dropLast, hl⟩

protected theorem tail {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.tail :=
  by
  cases' l with a l
  · simp [Config.NCap, Config.Cap] at h
  simp [Config.NCap] at *; cases' h with hc hl
  constructor; exact hc.tail; assumption

end NCap

namespace Cup

@[simp]
protected theorem nil : C.Cup [] := by rw [Config.Cup]; tauto

@[simp]
protected theorem singleton (a : α) : C.Cup [a] := by rw [Config.Cup]; simp

@[simp]
protected theorem pair {a b : α} : C.Cup [a, b] ↔ a < b := by rw [Config.Cup]; simp

@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cup (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.Cup (b::c::l) := by
  repeat' rw [Config.Cup]; simp
  tauto

@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cup (l1 ++ a::b::c::l2) ↔ C.Cup (l1 ++ [a, b]) ∧ C.Cup3 a b c ∧ C.Cup (b::c::l2) :=
  by
  induction' l1 with d l1 l1_ih
  · simp [Config.Cup]; tauto
  cases' l1 with e l1
  · simp [Config.Cup]; tauto
  cases' l1 with f l1
  · simp [Config.Cup]; tauto
  simp; simp at l1_ih; rw [l1_ih]; tauto

protected theorem dropLast {l : List α} (h : C.Cup l) : C.Cup l.dropLast := by
  induction' l with a l
  · simp
  cases' l with b l
  · simp
  cases' l with c l
  · simp
  cases' l with d l
  · simp [Config.Cap, List.dropLast] at *; tauto
  simp [List.dropLast] at *; tauto

protected theorem take {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.take n) :=
  ⟨h.left.take n, h.right.take n⟩

protected theorem drop {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.drop n) :=
  ⟨h.left.drop n, h.right.drop n⟩

protected theorem tail {l : List α} (h : C.Cup l) : C.Cup l.tail :=
  ⟨h.left.tail, h.right.tail⟩

theorem head?_lt_getLast? {l : List α} (l_cup : C.Cup l) (p q : α) (hl : 2 ≤ l.length)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q :=
  by
  cases' l with p l
  · simp at hp
  simp at hp; subst hp
  have l_nnil : l ≠ [] := by intro h; subst h; simp at hl
  rcases List.baek_takeLast l_nnil with ⟨q, l', eq_l⟩
  rw [eq_l] at hq; simp at hq; subst hq
  rw [Config.Cup, eq_l] at l_cup
  cases' l_cup with l_sorted _
  rw [List.isChain_iff_pairwise] at l_sorted; simp at l_sorted
  have h' := l_sorted.left q; tauto

end Cup

namespace NCup

@[simp]
protected theorem nil : C.NCup 0 [] := by rw [Config.NCup, Config.Cup]; tauto

@[simp]
protected theorem singleton (a : α) : C.NCup 1 [a] := by rw [Config.NCup, Config.Cup]; simp

@[simp]
protected theorem pair {a b : α} : C.NCup 2 [a, b] ↔ a < b := by
  rw [Config.NCup, Config.Cup]; simp

@[simp]
protected theorem cons3 {n : ℕ} {a b c : α} {l : List α} :
    C.NCup (n + 1) (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.NCup n (b::c::l) := by
  repeat' rw [Config.NCup, Config.Cup]; simp
  tauto

protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.dropLast :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  simp [Config.NCup] at *; cases' h with hc hl
  constructor; exact hc.dropLast; assumption

protected theorem dropLast_append_last {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (l' : List α) (a : α), l = l' ++ [a] ∧ C.NCup n l' :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  have nnil : (a::l) ≠ [] := by simp
  use(a::l).dropLast, (a::l).getLast nnil; constructor
  apply symm; exact List.dropLast_append_getLast nnil
  exact h.dropLast

protected theorem tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.tail :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  simp at *; cases' h with hc hl
  constructor; exact hc.tail; simp at hl; assumption

protected theorem cons_head_tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (a : α) (l' : List α), (l = a::l') ∧ C.NCup n l' :=
  by
  cases' l with a l
  · simp [Config.NCup, Config.Cup] at h
  exact ⟨a, l, rfl, h.1.tail, by simpa using h.2⟩

protected theorem take_head_last {n : ℕ} {l : List α} (h : C.NCup (n + 2) l) :
    ∃ (a : α) (l' : List α) (b : α), l = (a::l') ++ [b] ∧ C.NCup n l' :=
  by
  rcases h.cons_head_tail with ⟨a, l', eq_l, cup_l'⟩
  rcases cup_l'.dropLast_append_last with ⟨l'', b, eq_l', cup_l''⟩
  use a, l'', b; constructor
  rw [eq_l, eq_l']; simp; assumption

theorem take_left_with_head {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.head? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.head? :=
  by
  intro one_le_m m_le_n l_last
  use l.take m; refine' ⟨_, _, _⟩
  · exact List.take_subset m l
  · refine' ⟨h.left.take m, _⟩; simp; rw [h.right]; assumption
  · rw [← List.take_append_drop m l] at l_last
    rw [List.head?_append_of_ne_nil] at l_last; exact l_last
    rw [← h.right] at m_le_n
    intro hnil; simp at hnil
    cases' hnil with hnil hnil <;> subst hnil <;> try simp at m_le_n; linarith

theorem take_right_with_last {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.getLast? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.getLast? :=
  by
  intro one_le_m m_le_n l_last
  use l.drop (n - m); refine' ⟨_, _, _⟩
  · exact List.drop_subset (n - m) l
  · constructor; exact h.left.drop (n - m); simp; rw [h.right]
    exact Nat.sub_sub_self m_le_n
  · rw [← List.take_append_drop (n - m) l] at l_last
    rw [List.getLast?_append_of_ne_nil] at l_last; exact l_last
    rw [← h.right] at m_le_n
    intro hnil; rw [← List.reverse_eq_nil_iff, ← h.right] at hnil
    simp at hnil
    omega

theorem head?_lt_getLast? {n : ℕ} {l : List α} (l_ncup : C.NCup (n + 2) l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q :=
  by
  cases' l_ncup with l_cup l_length
  apply l_cup.head?_lt_getLast? p q
  rw [l_length]; exact le_add_self
  assumption; assumption

theorem head?_le_getLast? {n : ℕ} {l : List α} (l_ncup : C.NCup n l) (p q : α) (hp : p ∈ l.head?)
    (hq : q ∈ l.getLast?) : p ≤ q :=
  by
  have l_sorted : l.Pairwise (· < ·) :=
    by
    rw [← List.isChain_iff_pairwise]
    exact l_ncup.left.left
  cases' l_ncup with l_cup l_length
  cases' l with p l; simp at hp
  simp at hp; subst hp
  cases' l with p' l; simp at hq; subst hq; exact le_rfl
  rw [List.getLast?_cons_cons] at hq
  set l' := p'::l; clear_value l'
  simp at l_sorted
  apply le_of_lt; apply l_sorted.left
  exact List.mem_of_mem_getLast? hq

end NCup

end Config

theorem ncup_is_ngon {n : ℕ} {S : Finset α} (hn : 2 ≤ n) (h : C.HasNCup n S) : C.HasNGon n S :=
  by
  rcases h with ⟨c, ⟨⟨c_cup, c_length⟩, c_in_S⟩⟩
  have hc : c ≠ [] := by cases c; subst c_length; simp at hn; tauto
  rcases List.baek_takeLast hc with ⟨y, c, eq_c⟩; subst eq_c
  have hc : c ≠ [] := by
    intro h; subst c_length; subst h; simp at hn
  rcases List.baek_takeHead hc with ⟨x, c, eq_c⟩; subst eq_c
  clear hc
  use[x, y], (x::c) ++ [y]
  refine' ⟨_, _, _⟩; try simp; simp at c_in_S; tauto
  rw [Config.NGon, Config.Gon]; simp
  have hxy : x < y := by
    apply c_cup.head?_lt_getLast? x y <;> simp
  simp at c_length; rw [c_length]; constructor; tauto; linarith
  simp at c_in_S; simp; tauto
  exact c_in_S

theorem hasNCap_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCap n S1) :
    C.HasNCap n S2 := by
  cases' h1 with c1 h1
  use c1; constructor; exact h1.left
  intro a a_c1; exact h (h1.right a a_c1)

theorem hasNCup_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCup n S1) :
    C.HasNCup n S2 := by
  cases' h1 with c1 h1
  use c1; constructor; exact h1.left
  intro a a_c1; exact h (h1.right a a_c1)

theorem hasNGon_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNGon n S1) :
    C.HasNGon n S2 := by
  rcases h1 with ⟨c1, c2, ⟨gon, c1_in, c2_in⟩⟩
  exists c1, c2; refine' ⟨gon, _, _⟩
  intro a a_c1; apply h; exact c1_in a a_c1
  intro a a_c2; apply h; exact c2_in a a_c2

theorem hasNCup_le {n m : ℕ} {S : Finset α} (h : n ≤ m) : C.HasNCup m S → C.HasNCup n S :=
  by
  intro ngon
  rcases ngon with ⟨c, ⟨⟨c_cup, c_length⟩, c_in⟩⟩
  use c.take n; constructor
  · constructor; exact c_cup.take n; simp; rw [c_length]; exact h
  · intro a ha; apply c_in; exact List.take_subset _ _ ha

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Config/Mirror.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

-- BaekMirror configuration

variable {α : Type _} [LinearOrder α] (C : Config α)

open OrderDual

-- to_dual : α → αᵒᵈ
-- of_dual : αᵒᵈ → α
def Config.BaekMirror : Config (OrderDual α) :=
  ⟨BaekMirror3 C.Cup3, C.DecidableCup3.BaekMirror3⟩

variable {C}

@[simp]
def BaekMirror.cap {l : List α} : C.BaekMirror.Cap l.BaekMirror ↔ C.Cap l :=
  by
  constructor
  · rw [Config.Cap]; intro h; constructor
    exact List.isChain_mirror.mp h.left
    exact List.chain3'_mirror.mp h.right
  · intro h; rw [Config.Cap]; constructor
    exact List.isChain_mirror.mpr h.left
    exact List.chain3'_mirror.mpr h.right

@[simp]
def BaekMirror.cup {l : List α} : C.BaekMirror.Cup l.BaekMirror ↔ C.Cup l :=
  by
  constructor
  · rw [Config.Cup]; intro h; constructor
    exact List.isChain_mirror.mp h.left
    exact List.chain3'_mirror.mp h.right
  · intro h; rw [Config.Cup]; constructor
    exact List.isChain_mirror.mpr h.left
    exact List.chain3'_mirror.mpr h.right

@[simp]
def BaekMirror.gon {l1 l2 : List α} : C.BaekMirror.Gon l1.BaekMirror l2.BaekMirror ↔ C.Gon l1 l2 :=
  by
  rw [Config.Gon]; rw [Config.Gon]
  simp [List.BaekMirror_getLast?, List.BaekMirror_head?]
  have t_inj : Function.Injective (⇑toDual : α → αᵒᵈ) := fun a b => toDual_inj.mp
  have ot_inj := Option.map_injective t_inj
  rw [ot_inj.eq_iff]; rw [ot_inj.eq_iff]; tauto

@[simp]
def BaekMirror.ncap {n : ℕ} {l : List α} : C.BaekMirror.NCap n l.BaekMirror ↔ C.NCap n l := by
  rw [Config.NCap]; rw [Config.NCap]; simp

@[simp]
def BaekMirror.ncup {n : ℕ} {l : List α} : C.BaekMirror.NCup n l.BaekMirror ↔ C.NCup n l := by
  rw [Config.NCup]; rw [Config.NCup]; simp

@[simp]
def BaekMirror.ngon {n : ℕ} {l1 l2 : List α} : C.NGon n l1 l2 ↔ C.BaekMirror.NGon n l1.BaekMirror l2.BaekMirror :=
  by
  rw [Config.NGon]; rw [Config.NGon]
  rw [BaekMirror.gon]; simp

@[simp]
def BaekMirror.hasNCap {n : ℕ} {S : Finset α} : C.BaekMirror.HasNCap n S.BaekMirror ↔ C.HasNCap n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.ofBaekMirror
    constructor; rw [← BaekMirror.ncap]; convert c_ncap; simp
    rw [← @List.ofBaekMirrorBaekMirror α _ c] at c_in c_ncap
    set co := c.ofBaekMirror
    rw [← List.BaekMirror_in]; assumption
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.BaekMirror
    constructor; rw [BaekMirror.ncap]; tauto
    rw [List.BaekMirror_in]; assumption

@[simp]
def BaekMirror.hasNCup {n : ℕ} {S : Finset α} : C.BaekMirror.HasNCup n S.BaekMirror ↔ C.HasNCup n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.ofBaekMirror
    rw [← @List.ofBaekMirrorBaekMirror α _ c] at c_in c_ncup
    set co := c.ofBaekMirror
    rw [List.BaekMirror_in] at c_in
    rw [BaekMirror.ncup] at c_ncup; tauto
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.BaekMirror
    constructor; rw [BaekMirror.ncup]; tauto
    rw [List.BaekMirror_in]; assumption

def BaekMirror.hasNGon {n : ℕ} {S : Finset α} : C.BaekMirror.HasNGon n S.BaekMirror ↔ C.HasNGon n S :=
  by
  constructor
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.ofBaekMirror, c2.ofBaekMirror
    rw [← @List.ofBaekMirrorBaekMirror α _ c1] at c1_in c_ngon
    rw [← @List.ofBaekMirrorBaekMirror α _ c2] at c2_in c_ngon
    set c1o := c1.ofBaekMirror; set c2o := c2.ofBaekMirror
    rw [List.BaekMirror_in] at c1_in c2_in
    rw [← BaekMirror.ngon] at c_ngon; tauto
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.BaekMirror, c2.BaekMirror
    constructor; rw [← BaekMirror.ngon]; tauto
    simp [List.BaekMirror_in]; tauto

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Etv/Defs.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

variable {α : Type _} [LinearOrder α] (C : Config α)

namespace Config

def HasLaced (n : ℕ) (S : Finset α) (p q : α) : Prop :=
  ∃ (a b : ℕ) (cp c cq : List α) (hcp : C.NCup a cp) (hc : C.NCup n c) (hcQ : C.NCup b cq),
    (cp.baekIn S ∧ c.baekIn S ∧ cq.baekIn S) ∧
      a + b = n ∧ p ∈ cp.getLast? ∧ p ∈ c.head? ∧ q ∈ c.getLast? ∧ q ∈ cq.head?

theorem HasLaced.mem_ends {C : Config α} {n : ℕ} {S : Finset α} {p q : α} (h : C.HasLaced n S p q) :
    p ∈ S ∧ q ∈ S :=
  by
  rcases h with ⟨-, -, -, c, -, -, -, -, ⟨-, c_in_S, -⟩, -, ⟨-, c_head, c_last, -⟩⟩
  exact ⟨c_in_S _ (List.mem_of_mem_head? c_head), c_in_S _ (List.mem_of_mem_getLast? c_last)⟩

def HasInterweavedLaced (n : ℕ) (S : Finset α) (p q r s : α) : Prop :=
  (p < q ∧ q ≤ r ∧ r < s) ∧ C.HasLaced n S p r ∧ C.HasLaced n S q s

def HasJoin (a b : ℕ) (S : Finset α) : Prop :=
  ∃ (p : α) (cl cr : List α),
    (C.NCup a cl ∧ cl.baekIn S ∧ p ∈ cl.getLast?) ∧ C.NCup b cr ∧ cr.baekIn S ∧ p ∈ cr.head?

end Config

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Etv/Label.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

variable {α : Type _} [LinearOrder α] (C : Config α)

structure Config.Label (S : Finset α) where
  Slope : α → α → Prop
  -- The direction looks odd, but it is written in perspective of
  -- _where_ the edge ab is placed
  extend_left :
    ∀ {a b : α}, a ∈ S → b ∈ S → a < b → ¬Slope a b → ∀ {c : α}, c ∈ S → b < c → C.Cup3 a b c
  extend_right :
    ∀ {a b : α}, a ∈ S → b ∈ S → a < b → Slope a b → ∀ {c : α}, c ∈ S → c < a → C.Cup3 c a b

def Cap4FreeSlope {S : Finset α} (h : ¬C.HasNCap 4 S) (a b : α) : Prop :=
  ∀ c : S, ↑c < a → C.Cup3 c a b

instance decidableCap4FreeSlope {S : Finset α} (h : ¬C.HasNCap 4 S) :
    DecidableRel (Cap4FreeSlope C h) := fun a b => by rw [Cap4FreeSlope] <;> simp <;> infer_instance

variable {C}

def cap4FreeLabel {S : Finset α} (h : ¬C.HasNCap 4 S) : C.Label S :=
  by
  use Cap4FreeSlope C h
  · intro a b ha hb hab hn c hc hbc
    by_contra h'; apply hn; intro d hd
    by_contra h''; apply h; use[d, a, b, c]; simp [Config.NCap]; tauto
  · intro a b ha hb hab hy c hc hca
    exact hy ⟨c, hc⟩ hca

variable {C : Config α} {S : Finset α} {label : C.Label S}

protected theorem Config.Cup.extend_left {l : List α} (l_cup : C.Cup l) {a b : α}
    (s_ab : ¬label.Slope a b) (ha : a ∈ S) (hab : a < b) (l_in_S : l.baekIn S)
    (b_head_l : b ∈ l.head?) : C.Cup (a::l) :=
  by
  cases' l with b l
  · simp at b_head_l
  simp at b_head_l; subst b_head_l
  cases' l with c l
  · simp; exact hab
  simp at l_in_S; simp
  refine' ⟨_, _, _⟩ <;> try tauto
  simp [Config.Cup] at l_cup
  apply label.extend_left <;> tauto

protected theorem Config.Cup.extend_right {l : List α} (l_cup : C.Cup l) {a b : α}
    (s_ab : label.Slope a b) (hab : a < b) (hb : b ∈ S) (l_in_S : l.baekIn S)
    (a_last_l : a ∈ l.getLast?) : C.Cup (l ++ [b]) :=
  by
  by_cases hl : 2 ≤ l.length
  · rcases List.baek_takeLast2 hl with ⟨c, a, l', eq_l⟩
    rw [eq_l] at a_last_l; simp at a_last_l; subst a_last_l
    rw [eq_l]; simp; rw [← eq_l]
    refine' ⟨_, _, _⟩ <;> try tauto
    simp [Config.Cup] at l_cup
    rw [eq_l] at l_in_S; simp at l_in_S
    rw [eq_l] at l_cup; simp at l_cup
    apply label.extend_right <;> tauto
  cases' l with p l; simp
  cases' l with q l; simp at *; subst a_last_l <;> tauto
  exfalso; apply hl; exact le_add_self

protected theorem Config.NCup.extend_left {n : ℕ} {l : List α} (l_ncup : C.NCup n l) {a b : α}
    (s_ab : ¬label.Slope a b) (ha : a ∈ S) (hab : a < b) (l_in_S : l.baekIn S)
    (b_head_l : b ∈ l.head?) : C.NCup (n + 1) (a::l) :=
  by
  cases' l_ncup with l_cup l_len; constructor
  apply l_cup.extend_left s_ab <;> try assumption
  simp; assumption

protected theorem Config.NCup.extend_right {n : ℕ} {l : List α} (l_ncup : C.NCup n l) {a b : α}
    (s_ab : label.Slope a b) (hab : a < b) (hb : b ∈ S) (l_in_S : l.baekIn S)
    (a_last_l : a ∈ l.getLast?) : C.NCup (n + 1) (l ++ [b]) :=
  by
  cases' l_ncup with l_cup l_len; constructor
  apply l_cup.extend_right s_ab <;> try assumption
  simp; assumption

variable (label)

open OrderDual

protected def Config.Label.BaekMirror : C.BaekMirror.Label S.BaekMirror :=
  ⟨fun a b => ¬BaekMirror2 label.Slope a b,
    by
    intro a b a_in_S b_in_S hab hslope c c_in_S hbc
    simp [BaekMirror2] at hslope
    simp [Config.BaekMirror, BaekMirror3]
    simp [Finset.BaekMirror] at a_in_S b_in_S c_in_S
    rcases a_in_S with ⟨oa, ⟨oa_in_S, oa_eq⟩⟩
    rcases b_in_S with ⟨ob, ⟨ob_in_S, ob_eq⟩⟩
    rcases c_in_S with ⟨oc, ⟨oc_in_S, oc_eq⟩⟩
    rw [← oa_eq] at hab
    rw [← ob_eq] at hab hbc
    rw [← oc_eq] at hbc
    simp at hab hbc
    rw [← oa_eq, ← ob_eq, ← oc_eq]; simp
    rw [← oa_eq, ← ob_eq] at hslope; simp at hslope
    apply label.extend_right <;> tauto,
    by
    intro a b a_in_S b_in_S hab hslope c c_in_S hca
    simp [BaekMirror2] at hslope
    simp [Config.BaekMirror, BaekMirror3]
    simp [Finset.BaekMirror] at a_in_S b_in_S c_in_S
    rcases a_in_S with ⟨oa, ⟨oa_in_S, oa_eq⟩⟩
    rcases b_in_S with ⟨ob, ⟨ob_in_S, ob_eq⟩⟩
    rcases c_in_S with ⟨oc, ⟨oc_in_S, oc_eq⟩⟩
    rw [← oa_eq] at hab hca
    rw [← ob_eq] at hab
    rw [← oc_eq] at hca
    simp at hab hca
    rw [← oa_eq, ← ob_eq, ← oc_eq]; simp
    rw [← oa_eq, ← ob_eq] at hslope; simp at hslope
    apply label.extend_left <;> tauto⟩

variable {label}

def BaekMirror_slope {a b : α} : ¬label.BaekMirror.Slope (toDual b) (toDual a) ↔ label.Slope a b :=
  by
  rw [Config.Label.BaekMirror]; simp
  rw [BaekMirror2]; simp

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Etv/Mirror.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open OrderDual

variable {α : Type _} [LinearOrder α] {C : Config α}

def BaekMirror.hasLaced {n : ℕ} {S : Finset α} (p q : α) :
    C.BaekMirror.HasLaced n S.BaekMirror (toDual q) (toDual p) ↔ C.HasLaced n S p q :=
  by
  constructor
  · intro h; rcases h with ⟨b, a, cqm, cm, cpm, hcqm, hcm, hcpm, h⟩
    rw [← @List.ofBaekMirrorBaekMirror _ _ cpm] at hcpm h
    set cp := cpm.ofBaekMirror with eq_cp
    rw [BaekMirror.ncup] at hcpm
    rw [← @List.ofBaekMirrorBaekMirror _ _ cm] at hcm h
    set c := cm.ofBaekMirror with eq_c
    rw [BaekMirror.ncup] at hcm
    rw [← @List.ofBaekMirrorBaekMirror _ _ cqm] at hcqm h
    set cq := cqm.ofBaekMirror with eq_cq
    rw [BaekMirror.ncup] at hcqm
    use a, b, cp, c, cq, hcpm, hcm, hcqm
    repeat' rw [List.BaekMirror_in] at h
    simp [List.BaekMirror_getLast?, List.BaekMirror_head?] at h
    rcases h with ⟨hIn, ⟨eq_ab, h⟩⟩
    rw [add_comm] at eq_ab
    refine ⟨(by tauto), eq_ab, ?_⟩
    simp only [Option.mem_def]
    tauto
  · intro h; rcases h with ⟨a, b, cp, c, cq, hcp, hc, hcq, h⟩
    use b, a, cq.BaekMirror, c.BaekMirror, cp.BaekMirror
    refine' ⟨_, _, _, _⟩ <;> try rw [BaekMirror.ncup] <;> tauto
    repeat' rw [List.BaekMirror_mem_getLast?, List.BaekMirror_mem_head?]
    simp; simp at h; rw [Nat.add_comm b a]; tauto

def BaekMirror.hasInterweavedLaced {n : ℕ} {S : Finset α} (p q r s : α) :
    C.BaekMirror.HasInterweavedLaced n S.BaekMirror (toDual s) (toDual r) (toDual q) (toDual p) ↔
      C.HasInterweavedLaced n S p q r s :=
  by
  simp [Config.HasInterweavedLaced, BaekMirror.hasLaced]
  tauto

def BaekMirror.hasJoin {a b : ℕ} {S : Finset α} : C.BaekMirror.HasJoin b a S.BaekMirror ↔ C.HasJoin a b S :=
  by
  constructor
  · intro h; rcases h with ⟨pm, crm, clm, ⟨crm_cup, crm_in, crm_last⟩, ⟨clm_cup, clm_in, clm_head⟩⟩
    have eq_p := OrderDual.toDual_ofDual pm
    have eq_cl := @List.ofBaekMirrorBaekMirror _ _ clm
    have eq_cr := @List.ofBaekMirrorBaekMirror _ _ crm
    set p := ofDual pm
    set cl := clm.ofBaekMirror; set cr := crm.ofBaekMirror
    use p, cl, cr
    rw [← eq_p] at clm_head crm_last
    rw [← eq_cl] at clm_cup clm_in clm_head
    rw [← eq_cr] at crm_cup crm_in crm_last
    rw [BaekMirror.ncup] at clm_cup crm_cup
    rw [List.BaekMirror_in] at clm_in crm_in
    rw [List.BaekMirror_mem_head?] at clm_head
    rw [List.BaekMirror_mem_getLast?] at crm_last; tauto
  · intro h; rcases h with ⟨p, cl, cr, ⟨cl_cup, cl_in, cl_head⟩, ⟨cr_cup, cr_in, cr_last⟩⟩
    use toDual p, cr.BaekMirror, cl.BaekMirror
    rw [List.BaekMirror_mem_getLast?, List.BaekMirror_mem_head?]
    simp only [List.BaekMirror_in, BaekMirror.ncup, Option.mem_def]
    tauto

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Etv/AlphaBeta.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open scoped Classical

noncomputable section

variable {α : Type _} [LinearOrder α] {C : Config α} {S : Finset α} (l : C.Label S)

private theorem mem_imply_nnil {α : Type _} (a : α) {l : List α} (ha : a ∈ l) : l ≠ [] := by
  intro eq; subst eq; simp at ha

namespace Config.Label

def IsAlphaCup (a : α) (c : List α) : Prop :=
  (c ++ [a]).baekIn S ∧ (c ++ [a]).Pairwise (· < ·) ∧ (c ++ [a]).IsChain (l.Slopeᶜ)

theorem alphaCup_is_cup (c : List α) (c_in_S : c.baekIn S) (c_sorted : c.Pairwise (· < ·))
    (c_chain : c.IsChain (l.Slopeᶜ)) : C.Cup c :=
  by
  induction' c with h0 c ih; simp
  cases' c with h1 c; simp
  cases' c with h2 c
  · simp; simp at c_sorted; assumption
  simp; refine' ⟨_, _, _⟩
  simp at c_sorted <;> tauto
  simp at c_in_S c_chain c_sorted <;> apply l.extend_left <;> tauto
  apply ih <;> simp at c_in_S c_chain c_sorted ⊢ <;> tauto

def alphaCups' (a : α) : List (List α) :=
  (S.sort (· ≤ ·)).sublists.filter (l.IsAlphaCup a)

def alphaCup' (a : α) : Option (List α) :=
  (l.alphaCups' a).argmax List.length

def alphaCup'_isSome {a : α} (ha : a ∈ S) : Option.isSome (l.alphaCup' a) = true :=
  by
  rw [← Option.ne_none_iff_isSome, Config.Label.alphaCup']; simp
  apply mem_imply_nnil []; simp [IsAlphaCup, alphaCups']
  exact ha

-- one off from actual definition
def alpha (a : α) : ℕ :=
  if ha : a ∈ S then (Option.get _ (l.alphaCup'_isSome ha)).length else 0

-- APIs for alpha: First, existence of a cup with length alpha + 1
def alphaCup {a : α} (ha : a ∈ S) :
    Σ' c : List α,
      c.length = l.alpha a + 1 ∧ c.baekIn S ∧ c.Pairwise (· < ·) ∧ c.IsChain (l.Slopeᶜ) ∧ a ∈ c.getLast? :=
  by
  have some := l.alphaCup'_isSome ha
  set c := Option.get _ some with def_c
  rw [alpha]; rw [dif_pos ha]; rw [← def_c]
  have h_argmax := Option.get_mem some
  rw [← def_c, alphaCup'] at h_argmax
  have c_alpha_cup := List.argmax_mem h_argmax
  simp [alphaCups', IsAlphaCup] at c_alpha_cup
  use c ++ [a]; simp; tauto

-- Next, maximality of the cup with length alpha + 1
def cup_length_le_alpha {a : α} {c : List α} (c_in_S : c.baekIn S) (c_sorted : c.Pairwise (· < ·))
    (c_chain : c.IsChain (l.Slopeᶜ)) (c_last : a ∈ c.getLast?) : c.length ≤ l.alpha a + 1 :=
  by
  have ha : a ∈ S := c_in_S _ (List.mem_of_mem_getLast? c_last)
  have some := l.alphaCup'_isSome ha
  set d := Option.get _ some with def_d
  rw [alpha]; rw [dif_pos ha]; rw [← def_d]
  have h_argmax := Option.get_mem some
  rw [← def_d, alphaCup'] at h_argmax
  rcases List.baek_takeLast' c_last with ⟨c', eq_c⟩
  subst eq_c; simp
  have c'_alpha_cup : c' ∈ l.alphaCups' a :=
    by
    rw [alphaCups']; simp; constructor
    · apply List.sublist_of_subperm_of_pairwise _ _ (Finset.sortedLT_sort S).pairwise
      apply List.Nodup.subperm
      apply @List.Nodup.sublist _ _ (c' ++ [a])
      simp; exact List.Pairwise.nodup c_sorted
      intro a ha; simp; simp at c_in_S; exact c_in_S.left _ ha
      apply List.Pairwise.sublist _ c_sorted; simp
    · refine' ⟨_, _, _⟩ <;> assumption
  exact List.le_of_mem_argmax c'_alpha_cup h_argmax

theorem add_alpha {a : α} (ha : a ∈ S) {n : ℕ} {c : List α} (c_in_S : c.baekIn S) (c_cup : C.NCup n c)
    (c_head : a ∈ c.head?) : C.HasNCup (n + l.alpha a) S :=
  by
  rcases l.alphaCup ha with ⟨d, d_length, d_in_S, d_sorted, d_chain, d_last⟩
  have d_cup : C.Cup d := l.alphaCup_is_cup _ d_in_S d_sorted d_chain
  rcases List.baek_takeLast' d_last with ⟨d', eq_d⟩
  rcases List.baek_takeHead' c_head with ⟨c', eq_c⟩
  use d' ++ a::c'
  by_cases hd' : d' = []
  · subst hd'; simp at eq_d; subst eq_d; simp at d_length; rw [d_length]
    rw [← eq_c]; constructor <;> simp <;> assumption
  rcases List.baek_takeLast hd' with ⟨p, d'', eq_d'⟩
  cases' c' with q c''
  · subst eq_c; cases' c_cup with _ c_len; simp at c_len
    subst c_len; rw [← eq_d]; refine' ⟨⟨_, _⟩, _⟩
    assumption; rw [d_length]; exact add_comm _ _; assumption
  rw [eq_d']; constructor
  · rw [Config.NCup]; constructor; simp; refine' ⟨_, _, _⟩
    convert d_cup; rw [eq_d, eq_d']; simp
    rw [eq_d'] at eq_d; simp at eq_d
    rw [eq_d] at d_chain d_sorted d_in_S
    rw [eq_c] at c_in_S c_cup
    rw [Config.NCup, Config.Cup] at c_cup
    apply l.extend_left
    simp at d_in_S <;> tauto; simp at d_in_S <;> tauto
    have t := @List.Pairwise.sublist _ [p, a] (d'' ++ [p, a]) _ ?_ d_sorted
    simp at t; exact t; simp
    simp at d_chain <;> tauto
    simp at c_in_S <;> tauto
    simp at c_cup <;> tauto
    rw [← eq_c]; exact c_cup.left
    rw [eq_d] at d_length; simp at d_length
    rw [← eq_c]; rw [← eq_d']; simp; rw [d_length]
    rw [c_cup.right]; exact add_comm _ _
  · rw [← eq_c]; rw [← eq_d']; simp; rw [eq_d] at d_in_S
    simp at d_in_S; tauto

end Config.Label

namespace Config

variable (C) (S)

def IsBetaCup (a : α) (c : List α) : Prop :=
  (c ++ [a]).baekIn S ∧ C.Cup (c ++ [a])

instance decidableIsBetaCup (a : α) (c : List α) : Decidable (C.IsBetaCup S a c) := by
  rw [IsBetaCup] <;> infer_instance

def betaCups' (a : α) : List (List α) :=
  (S.sort (· ≤ ·)).sublists.filter (C.IsBetaCup S a)

def betaCup' (a : α) : Option (List α) :=
  (C.betaCups' S a).argmax List.length

def betaCup'_isSome {a : α} (ha : a ∈ S) : Option.isSome (C.betaCup' S a) :=
  by
  rw [← Option.ne_none_iff_isSome]; rw [Config.betaCup']; simp
  apply mem_imply_nnil []; simp [IsBetaCup, betaCups']; exact ha

-- one off from actual definition
def beta (a : α) : ℕ :=
  if ha : a ∈ S then (Option.get _ (C.betaCup'_isSome S ha)).length else 0

-- APIs for beta: First, existence of a cup with length alpha + 1
def betaCup {a : α} (ha : a ∈ S) :
    Σ' c : List α, c.baekIn S ∧ C.NCup (C.beta S a + 1) c ∧ a ∈ c.getLast? :=
  by
  have some := C.betaCup'_isSome S ha
  set c := Option.get _ some with def_c
  rw [beta]; rw [dif_pos ha]; rw [← def_c]
  have h_argmax := Option.get_mem some
  rw [← def_c, betaCup'] at h_argmax
  have c_beta_cup := List.argmax_mem h_argmax
  simp [betaCups', IsBetaCup] at c_beta_cup
  use c ++ [a]; simp [Config.NCup]; tauto

theorem has_beta_cup {a : α} (ha : a ∈ S) : C.HasNCup (C.beta S a + 1) S :=
  by
  rcases C.betaCup S ha with ⟨c, c_in, c_cup, -⟩
  use c

-- Next, maximality of the cup with length alpha + 1
def cup_length_le_beta {a : α} {c : List α} (c_in_S : c.baekIn S) (c_cup : C.Cup c)
    (c_last : a ∈ c.getLast?) : c.length ≤ C.beta S a + 1 :=
  by
  have ha : a ∈ S := c_in_S _ (List.mem_of_mem_getLast? c_last)
  have some := C.betaCup'_isSome S ha
  set d := Option.get _ some with def_d
  rw [beta]; rw [dif_pos ha]; rw [← def_d]
  have h_argmax := Option.get_mem some
  rw [← def_d, betaCup'] at h_argmax
  rcases List.baek_takeLast' c_last with ⟨c', eq_c⟩
  subst eq_c; simp
  have c_sorted := List.isChain_iff_pairwise.mp c_cup.left
  have c'_beta_cup : c' ∈ C.betaCups' S a :=
    by
    rw [betaCups']; simp; constructor
    · apply List.sublist_of_subperm_of_pairwise _ _ (Finset.sortedLT_sort S).pairwise
      apply List.Nodup.subperm
      apply @List.Nodup.sublist _ _ (c' ++ [a]); simp
      exact List.Pairwise.nodup c_sorted
      intro a ha; simp; simp at c_in_S; exact c_in_S.left _ ha
      apply List.Pairwise.sublist _ c_sorted; simp
    · constructor <;> assumption
  exact List.le_of_mem_argmax c'_beta_cup h_argmax

end Config

theorem Config.Label.alpha_le_beta {a : α} (ha : a ∈ S) : l.alpha a ≤ C.beta S a :=
  by
  rcases l.alphaCup ha with ⟨c, c_length, c_in, c_sorted, c_chain, c_last⟩
  have c_cup := l.alphaCup_is_cup _ c_in c_sorted c_chain
  have ineq := C.cup_length_le_beta S c_in c_cup c_last
  rw [c_length] at ineq; simp at ineq; exact ineq

variable {l}

theorem slope_ff_inc_alpha {a b : α} (sab : ¬l.Slope a b) (ha : a ∈ S) (hb : b ∈ S)
    (a_le_b : a < b) : l.alpha a < l.alpha b :=
  by
  rcases l.alphaCup ha with ⟨c, c_length, c_in, c_sorted, c_chain, c_last⟩
  rcases List.baek_takeLast' c_last with ⟨c', c_eq⟩
  rw [Nat.lt_iff_add_one_le, ← add_le_add_iff_right 1]
  set d := c ++ [b] with def_d
  have d_length : d.length = l.alpha a + 1 + 1 := by simp [def_d, c_length]
  rw [← d_length]
  apply l.cup_length_le_alpha
  · rw [def_d]; simp; tauto
  · rw [def_d, c_eq, ← List.isChain_iff_pairwise]
    simp; rw [List.isChain_iff_pairwise]
    rw [← c_eq]; exact ⟨c_sorted, a_le_b⟩
  · rw [def_d, c_eq]; simp; rw [← c_eq]
    exact ⟨c_chain, sab⟩
  · rw [def_d]; simp

theorem slope_tt_inc_beta {a b : α} (sab : l.Slope a b) (ha : a ∈ S) (hb : b ∈ S) (a_le_b : a < b) :
    C.beta S a < C.beta S b :=
  by
  rcases C.betaCup S ha with ⟨c, c_in, ⟨c_cup, c_length⟩, c_last⟩
  rcases List.baek_takeLast' c_last with ⟨c', c_eq⟩
  rw [Nat.lt_iff_add_one_le, ← add_le_add_iff_right 1]
  set d := c ++ [b] with def_d
  have d_length : d.length = C.beta S a + 1 + 1 := by simp [def_d, c_length]
  rw [← d_length]
  apply C.cup_length_le_beta S <;> rw [def_d]
  simp; constructor <;> assumption
  apply c_cup.extend_right sab <;> try assumption
  simp

variable (C)

theorem Config.alpha_eq_beta_inc {a b : α} (ha : a ∈ S) (hb : b ∈ S) (h : l.alpha a = l.alpha b) :
    a < b ↔ C.beta S a < C.beta S b := by
  constructor
  · intro hab
    by_cases hl : l.Slope a b
    apply slope_tt_inc_beta hl <;> assumption
    have h' := slope_ff_inc_alpha hl ha hb hab
    rw [h] at h'; simp at h'
  · intro hab
    rcases lt_trichotomy a b with (a_lt_b | a_eq_b | b_lt_a)
    exact a_lt_b
    subst a_eq_b; simp at hab
    exfalso; by_cases hl : l.Slope b a
    have h' := slope_tt_inc_beta hl hb ha b_lt_a
    have h'' := lt_trans h' hab; simp at h''
    have h' := slope_ff_inc_alpha hl hb ha b_lt_a
    rw [h] at h'; simp at h'

variable {C} (l)

theorem Config.Label.beta_eq_alpha_inc {a b : α} (ha : a ∈ S) (hb : b ∈ S)
    (h : C.beta S a = C.beta S b) : a < b ↔ l.alpha a < l.alpha b :=
  by
  constructor
  · intro hab
    by_cases hl : l.Slope a b
    have h' := slope_tt_inc_beta hl ha hb hab
    rw [h] at h'; simp at h'
    apply slope_ff_inc_alpha hl <;> assumption
  · intro hab
    rcases lt_trichotomy a b with (a_lt_b | a_eq_b | b_lt_a)
    exact a_lt_b
    subst a_eq_b; simp at hab
    exfalso; by_cases hl : l.Slope b a
    have h' := slope_tt_inc_beta hl hb ha b_lt_a
    rw [h] at h'; simp at h'
    have h' := slope_ff_inc_alpha hl hb ha b_lt_a
    have h'' := lt_trans h' hab; simp at h''
end

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Main/Defs.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open scoped Classical

noncomputable section

variable {α : Type _} [LinearOrder α] (C : Config α)

def Config.MainGoal (n : ℕ) : Prop :=
  ∀ S : Finset α,
    Nat.choose (n + 2) 2 + 2 ≤ S.card →
      ¬C.HasNCap 4 S → ¬C.HasNCup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s

def Config.MainGoalWlog (n : ℕ) : Prop :=
  ∀ S : Finset α,
    ¬C.HasJoin (n + 2) (n + 1) S →
      Nat.choose (n + 2) 2 + 2 ≤ S.card →
        ¬C.HasNCap 4 S → ¬C.HasNCup (n + 3) S → ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s
end

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Main/Lemmas/JoinN2N2.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.join_n2_n2_case_ff (S : Finset α) (n : ℕ) (a x b : α) (c1 c2 : List α)
    (lab : C.Label S) (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
    (hc1 : C.NCup (n + 2) (c1 ++ [a, x])) (c1_in_S : c1.baekIn S) (hc2 : C.NCup (n + 2) (x::b::c2))
    (c2_in_S : c2.baekIn S) (sab : ¬lab.Slope a b) : C.HasNGon (n + 3) S :=
  by
  have hax : a < x := by simp [Config.Cup, Config.NCup] at hc1 <;> tauto
  have hxb : x < b := by simp [Config.Cup, Config.NCup] at hc2 <;> tauto
  have hab : a < b := LT.lt.trans hax hxb
  have h_b_c2 : (b::c2) ≠ [] := by simp
  rcases List.baek_takeLast h_b_c2 with ⟨c, c3, eq_c2⟩
  rw [eq_c2] at hc2
  have hxc : x < c := by apply hc2.head?_lt_getLast? x c <;> simp <;> decide
  have c_in_S : c ∈ S := by
    have h_in : (b::c2).baekIn S := by simp; tauto
    rw [eq_c2] at h_in; simp at h_in; tauto
  by_cases haxc : C.Cup3 a x c
  · apply ncup_is_ngon; simp
    use c1 ++ [a, x, c]; constructor; constructor
    simp; rw [Config.NCup] at hc1; tauto
    simp; simp [Config.NCup] at hc1; tauto
    simp; tauto
  · use[a, x, c], a::c3 ++ [c]
    refine' ⟨⟨_, _⟩, _, _⟩ <;> try simp; try tauto
    constructor; tauto
    rw [← eq_c2]; rw [← eq_c2] at hc2
    have hbc2 := hc2.tail.left; simp at hbc2
    apply hbc2.extend_left sab <;> try tauto
    simp; tauto; simp [Config.NCup] at hc2
    ring_nf; simp; exact hc2.right
    constructor; assumption
    have hh : (b::c2).baekIn S := by simp; tauto
    rw [eq_c2] at hh; simp at hh; exact hh

theorem Config.join_n2_n2_case_tt (S : Finset α) (n : ℕ) (a x b : α) (c1 c2 : List α)
    (lab : C.Label S) (a_in_S : a ∈ S) (x_in_S : x ∈ S) (b_in_S : b ∈ S)
    (hc1 : C.NCup (n + 2) (c1 ++ [a, x])) (c1_in_S : c1.baekIn S) (hc2 : C.NCup (n + 2) (x::b::c2))
    (c2_in_S : c2.baekIn S) (hab : lab.Slope a b) : C.HasNGon (n + 3) S :=
  by
  rw [← Finset.memBaekMirror] at a_in_S x_in_S b_in_S
  rw [← BaekMirror.ncup] at hc1 hc2
  rw [← List.BaekMirror_in] at c1_in_S c2_in_S
  simp at hc1 hc2
  have hba := hab; rw [← BaekMirror_slope] at hba
  have BaekMirrored_goal :=
    C.BaekMirror.join_n2_n2_case_ff S.BaekMirror n (toDual b) (toDual x) (toDual a) c2.BaekMirror c1.BaekMirror
      lab.BaekMirror b_in_S x_in_S a_in_S hc2 c2_in_S hc1 c1_in_S hba
  rw [BaekMirror.hasNGon] at BaekMirrored_goal
  tauto

theorem Config.join_n2_n2 (S : Finset α) {n : ℕ} (cap4_free : ¬C.HasNCap 4 S) {c1 : List α}
    (hc1 : C.NCup (n + 2) c1) (c1_in_S : c1.baekIn S) {c2 : List α} (hc2 : C.NCup (n + 2) c2)
    (c2_in_S : c2.baekIn S) (x : α) (hx1 : x ∈ c1.getLast?) (hx2 : x ∈ c2.head?) :
    C.HasNGon (n + 3) S :=
  by
  -- Introduce variables
  have c1_size2 : 2 ≤ c1.length := by cases hc1 <;> linarith
  rcases List.baek_takeLast2 c1_size2 with ⟨a, x, c1', eq_c1⟩
  subst eq_c1; simp at hx1; subst hx1
  have c2_size2 : 2 ≤ c2.length := by cases hc2 <;> linarith
  rcases List.baek_takeHead2 c2_size2 with ⟨x, b, c2', eq_c2⟩
  subst eq_c2; simp at hx2; subst hx2
  have lab := cap4FreeLabel cap4_free
  by_cases hl : lab.Slope a b
  · apply C.join_n2_n2_case_tt S n a x b c1' c2' lab <;> simp at c1_in_S c2_in_S <;> tauto
  · apply C.join_n2_n2_case_ff S n a x b c1' c2' lab <;> simp at c1_in_S c2_in_S <;> tauto

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Main/Lemmas/JoinN2N3N2.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.join_n2_n3_n2_ff (S : Finset α) (cap4_free : ¬C.HasNCap 4 S) {n : ℕ} (x y : α)
    {P : List α} (hPx : C.NCup (n + 2) (P ++ [x])) (Px_in_S : (P ++ [x]).baekIn S) {Q : List α}
    (hxQy : C.NCup (n + 3) ((x::Q) ++ [y])) (xQy_in_S : ((x::Q) ++ [y]).baekIn S) {R : List α}
    (hyR : C.NCup (n + 2) (y::R)) (yR_in_S : (y::R).baekIn S) (label : C.Label S)
    (sxy : ¬label.Slope x y) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  have x_in_S : x ∈ S := by simp at xQy_in_S <;> tauto
  have y_in_S : y ∈ S := by simp at xQy_in_S <;> tauto
  have x_lt_y : x < y := by apply hxQy.head?_lt_getLast? x y <;> simp
  have hP := hPx.dropLast; simp at hP
  have hQy := hxQy.tail; simp at hQy
  rcases hP.dropLast_append_last with ⟨P', a, eq_P, hP'⟩; subst eq_P
  rcases hQy.cons_head_tail with ⟨b, Q', eq_Q, hQ'⟩
  have eq_xQy : (x::Q) ++ [y] = x::(Q ++ [y]) := by simp
  rw [eq_xQy] at hxQy xQy_in_S; clear eq_xQy
  rw [eq_Q] at hxQy xQy_in_S;
  have a_in_S : a ∈ S := by simp at Px_in_S <;> tauto
  have b_in_S : b ∈ S := by simp at xQy_in_S <;> tauto
  have hR := hyR.tail; simp at hR
  rcases hR.dropLast_append_last with ⟨R', z, eq_R, hR'⟩
  have xy_laced : C.HasLaced (n + 3) S x y :=
    by
    have hy : C.NCup 1 [y] := by simp
    exists _, _, _, _, _, hPx, hxQy, hy
    refine' ⟨_, _, _⟩
    constructor; assumption; constructor; assumption
    simp; simp at xQy_in_S; tauto
    simp; simp
    rw [←eq_Q]; simp
  have xz_laced : C.HasLaced (n + 3) S x z :=
    by
    have hxyR : C.NCup (n + 3) (x::y::R) := by
      apply hyR.extend_left sxy <;> try assumption
      simp
    rw [eq_R] at hxyR
    have hz : C.NCup 1 [z] := by simp
    exists _, _, _, _, _, hPx, hxyR, hz
    refine' ⟨_, _, _⟩
    constructor; assumption; rw [eq_R] at yR_in_S
    simp; simp at yR_in_S; tauto
    simp; simp
  have a_lt_x : a < x := by rw [Config.NCup, Config.Cup] at hPx <;> simp at hPx <;> tauto
  have x_lt_b : x < b := by rw [Config.NCup, Config.Cup] at hxQy <;> simp at hxQy <;> tauto
  have y_lt_z : y < z := by
    rw [eq_R] at hyR; apply hyR.head?_lt_getLast? y z
    simp; simp
  have a_lt_b : a < b := LT.lt.trans a_lt_x x_lt_b
  by_cases sab : label.Slope a b; swap
  -- case ¬label.Slope a b
  · have hQy := hxQy.tail; simp at hQy
    have haQy : C.NCup (n + 3) ((a::Q) ++ [y]) :=
      by
      rw [←eq_Q] at hQy xQy_in_S
      apply hQy.extend_left sab <;> try assumption
      simp; simp at xQy_in_S; tauto;
      rw [eq_Q]; simp
    have ha : C.NCup 1 [a] := by simp
    have ay_laced : C.HasLaced (n + 3) S a y :=
      by
      exists _, _, _, _, _, ha, haQy, hyR
      refine' ⟨_, _, _⟩
      simp; rw [← eq_Q] at xQy_in_S; simp at xQy_in_S yR_in_S; tauto
      rw [Nat.add_comm]; simp
    use a, x, y, z; constructor
    · constructor; assumption; constructor
      exact le_of_lt x_lt_y; assumption
    · tauto
  -- case label.Slope a b
  have b_lt_y : b < y := by
    have hQy := hxQy.tail; simp at hQy
    apply hQy.head?_lt_getLast? b y <;> simp
    rw [← eq_Q]; simp
  have hP := hPx.dropLast; simp at hP
  have hPb : C.NCup (n + 2) (P' ++ [a] ++ [b]) :=
    by
    apply hP.extend_right sab <;> try assumption
    simp <;> simp at Px_in_S <;> tauto
    simp
  by_cases sby : label.Slope b y; swap
  · have bz_laced : C.HasLaced (n + 3) S b z :=
      by
      have hbyR : C.NCup (n + 3) (b::y::R) := by
        apply hyR.extend_left sby <;> try assumption
        simp
      have hz : C.NCup 1 [z] := by simp
      exists _, _, _, _, _, hPb, hbyR, hz; rw [eq_R]
      refine' ⟨_, _, _⟩
      rw [eq_R] at yR_in_S; simp at Px_in_S yR_in_S; simp; tauto
      simp; simp
    use x, b, y, z; constructor
    constructor; assumption; constructor; apply le_of_lt; assumption; assumption
    tauto
  · have hPby : C.NCup (n + 3) (P' ++ [a] ++ [b] ++ [y]) :=
      by
      apply hPb.extend_right sby <;> try assumption
      simp <;> simp at Px_in_S <;> tauto; simp
    have P_nnil : P' ++ [a] ≠ [] := by simp
    rcases List.baek_takeHead P_nnil with ⟨w, P_, eq_P_⟩
    rw [eq_P_] at hPby
    have wy_laced : C.HasLaced (n + 3) S w y :=
      by
      have hw : C.NCup 1 [w] := by simp
      exists _, _, _, _, _, hw, hPby, hyR
      refine' ⟨_, _, _⟩
      rw [eq_P_] at Px_in_S; simp at yR_in_S Px_in_S; simp; tauto
      rw [Nat.add_comm]; simp
    use w, x, y, z; constructor; constructor
    rw [eq_P_] at hPx; apply hPx.head?_lt_getLast? w x <;> simp
    constructor; exact le_of_lt x_lt_y; assumption; tauto

theorem Config.join_n2_n3_n2_tt (S : Finset α) (cap4_free : ¬C.HasNCap 4 S) {n : ℕ} (x y : α)
    {P : List α} (hPx : C.NCup (n + 2) (P ++ [x])) (Px_in_S : (P ++ [x]).baekIn S) {Q : List α}
    (hxQy : C.NCup (n + 3) ((x::Q) ++ [y])) (xQy_in_S : ((x::Q) ++ [y]).baekIn S) {R : List α}
    (hyR : C.NCup (n + 2) (y::R)) (yR_in_S : (y::R).baekIn S) (label : C.Label S)
    (sxy : label.Slope x y) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  have BaekMirrored_goal : ∃ s r q p, C.BaekMirror.HasInterweavedLaced (n + 3) S.BaekMirror s r q p :=
    by
    rw [← BaekMirror.ncup] at hPx hxQy hyR; simp at hPx hxQy hyR
    rw [← BaekMirror.hasNCap] at cap4_free
    rw [← List.BaekMirror_in] at Px_in_S xQy_in_S yR_in_S
    simp [-List.baek_cons_in, -List.baek_append_in] at Px_in_S xQy_in_S yR_in_S
    have syx := sxy; rw [← BaekMirror_slope] at syx
    apply
        C.BaekMirror.join_n2_n3_n2_ff _ _ (toDual y) (toDual x) hyR _ hxQy _ hPx _ label.BaekMirror _ <;>
      assumption
  simp at BaekMirrored_goal
  rcases BaekMirrored_goal with ⟨s, r, q, p, h⟩
  rw [BaekMirror.hasInterweavedLaced] at h
  use p, q, r, s

theorem Config.join_n2_n3_n2 (S : Finset α) {n : ℕ} (cap4_free : ¬C.HasNCap 4 S)
    (cup_free : ¬C.HasNCup (n + 4) S) {cx : List α} (cx_ncup : C.NCup (n + 2) cx)
    (cx_in_S : cx.baekIn S) {c : List α} (c_ncup : C.NCup (n + 3) c) (c_in_S : c.baekIn S) {cy : List α}
    (cy_ncup : C.NCup (n + 2) cy) (cy_in_S : cy.baekIn S) (x : α) (hxcx : x ∈ cx.getLast?)
    (hxc : x ∈ c.head?) (y : α) (hyc : y ∈ c.getLast?) (hycy : y ∈ cy.head?) :
    ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  rcases c_ncup.take_head_last with ⟨x, Q, y, eq_Q, Q_ncup⟩
  subst eq_Q; simp at hxc hyc; subst hxc; subst hyc
  rcases cx_ncup.dropLast_append_last with ⟨P, x, eq_P, P_ncup⟩
  subst eq_P; simp at hxcx; subst hxcx
  rcases cy_ncup.cons_head_tail with ⟨y, R, eq_R, R_ncup⟩
  subst eq_R; simp at hycy; subst hycy
  have label := cap4FreeLabel cap4_free
  by_cases sxy : label.Slope x y
  · apply C.join_n2_n3_n2_tt S <;> try assumption
  · apply C.join_n2_n3_n2_ff S <;> try assumption

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Main/Lemmas/InterweavedLacedNgon.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.hasInterweavedLaced_hasNGon_ff {n : ℕ} {S : Finset α} (cap4_free : ¬C.HasNCap 4 S)
    {p q r s : α} (label : C.Label S) (q_lt_r : q < r) (sqr : ¬label.Slope q r) :
    C.HasInterweavedLaced (n + 2) S p q r s → C.HasNGon (n + 3) S :=
  by
  intro h; rcases h with ⟨⟨p_lt_q, q_le_r, r_lt_s⟩, ⟨pr_laced, qs_laced⟩⟩
  rcases pr_laced with
    ⟨a, b, cp, c1, cr, hcp, hc1, hcr,
      ⟨⟨cp_in_S, c1_in_S, cr_in_S⟩, eq_ab, cp_last, c1_head, c1_last, cr_head⟩⟩
  rcases qs_laced with
    ⟨c, d, cq, c2, cs, hcq, hc2, hcs,
      ⟨⟨cq_in_S, c2_in_S, cs_in_S⟩, eq_cd, cq_last, c2_head, c2_last, cs_head⟩⟩
  have p_in_S : p ∈ S := by
    apply c1_in_S
    exact List.mem_of_mem_head? c1_head
  have q_in_S : q ∈ S := by
    apply c2_in_S
    exact List.mem_of_mem_head? c2_head
  have r_in_S : r ∈ S := by
    apply c1_in_S
    exact List.mem_of_mem_getLast? c1_last
  have s_in_S : s ∈ S := by
    apply c2_in_S
    exact List.mem_of_mem_getLast? c2_last
  have label := cap4FreeLabel cap4_free
  by_cases spq : label.Slope p q; swap
  · apply ncup_is_ngon; linarith
    use p::c2; constructor
    apply hc2.extend_left spq <;> assumption
    simp; tauto
  -- (spq : ¬label.Slope p q) from now on
  by_cases cpqr : C.Cup3 p q r
  · apply ncup_is_ngon; linarith
    use cp ++ q::cr; constructor; swap; simp; tauto
    have cp_nnil : cp ≠ [] := by intro h; subst h; simp at cp_last
    rcases List.baek_takeLast cp_nnil with ⟨p, cp', eq_cp⟩
    rw [eq_cp] at cp_last; simp at cp_last; subst cp_last
    -- idea: implement a lemma for taking explicit head
    -- from a statement like this
    have cr_nnil : cr ≠ [] := by intro h; subst h; simp at cr_head
    rcases List.baek_takeHead cr_nnil with ⟨r, cr', eq_cr⟩; constructor
    rw [eq_cr] at cr_head; simp at cr_head; subst cr_head
    rw [eq_cp, eq_cr]; simp
    refine' ⟨_, _, _⟩; swap; assumption
    have eq : cp' ++ [p, q] = cp' ++ [p] ++ [q] := by simp
    rw [eq]; rw [← eq_cp]
    apply hcp.left.extend_right spq <;> try assumption
    rw [eq_cp]; simp
    rw [← eq_cr]
    apply hcr.left.extend_left sqr <;> try assumption
    rw [eq_cr]; simp
    simp; rw [hcp.right, hcr.right]; linarith
  · use[p, q, r], c1; constructor; swap; simp; tauto
    constructor; swap; rw [hc1.right]; simp; linarith
    rw [Config.Gon]; simp
    cases' hc1 with c1_cup c1_length; rw [c1_length]
    simp at c1_head c1_last
    have h2n : 2 ≤ n + 2 := le_add_self; tauto

theorem Config.hasInterweavedLaced_hasNGon_tt {n : ℕ} {S : Finset α} (cap4_free : ¬C.HasNCap 4 S)
    {p q r s : α} (label : C.Label S) (q_lt_r : q < r) (sqr : label.Slope q r) :
    C.HasInterweavedLaced (n + 2) S p q r s → C.HasNGon (n + 3) S :=
  by
  rw [← BaekMirror.hasInterweavedLaced, ← BaekMirror.hasNGon]
  have srq := sqr; rw [← BaekMirror_slope] at srq
  rw [← BaekMirror.hasNCap] at cap4_free
  apply C.BaekMirror.hasInterweavedLaced_hasNGon_ff <;> assumption

theorem Config.hasInterweavedLaced_hasNGon {n : ℕ} {S : Finset α} (cap4_free : ¬C.HasNCap 4 S)
    {p q r s : α} : C.HasInterweavedLaced (n + 2) S p q r s → C.HasNGon (n + 3) S :=
  by
  intro h; have q_le_r : q ≤ r := by rw [Config.HasInterweavedLaced] at h <;> tauto
  rw [le_iff_eq_or_lt] at q_le_r
  rcases q_le_r with q_eq_r | q_lt_r
  · subst q_eq_r; rcases h with ⟨-, pr_laced, qs_laced⟩
    rcases pr_laced with ⟨-, -, -, c1, -, -, hc1, -, ⟨-, c1_in_S, -⟩, -, ⟨-, c1_head, c1_last, -⟩⟩
    rcases qs_laced with ⟨-, -, -, c2, -, -, hc2, -, ⟨-, c2_in_S, -⟩, -, ⟨-, c2_head, c2_last, -⟩⟩
    apply C.join_n2_n2 S cap4_free hc1 c1_in_S hc2 c2_in_S q c1_last c2_head
  have label := cap4FreeLabel cap4_free
  by_cases sqr : label.Slope q r
  · revert h
    apply C.hasInterweavedLaced_hasNGon_tt <;> assumption
  · revert h
    apply C.hasInterweavedLaced_hasNGon_ff <;> assumption

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Main/Lemmas/JoinN2N3JoinN3N2.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open OrderDual

variable {α : Type _} [LinearOrder α] (C : Config α)

theorem Config.join_n2_n2_interweaved {S : Finset α} {n : ℕ} {c1 : List α}
    (c1_cup : C.NCup (n + 2) c1) (c1_in_S : c1.baekIn S) {c2 : List α} (c2_cup : C.NCup (n + 2) c2)
    (c2_in_S : c2.baekIn S) (x : α) (c1_last : x ∈ c1.getLast?) (c2_head : x ∈ c2.head?) :
    ∃ p q r s, C.HasInterweavedLaced (n + 2) S p q r s :=
  by
  rcases c1_cup.take_head_last with ⟨p, c1', q, eq_c1, c1'_cup⟩
  rcases c2_cup.take_head_last with ⟨q, c2', r, eq_c2, c2'_cup⟩
  rw [eq_c1] at c1_last; rw [eq_c2] at c2_head
  simp at c1_last c2_head; subst c1_last; subst c2_head
  use p, q, q, r; refine' ⟨_, _, _⟩
  · refine' ⟨_, _, _⟩
    rw [eq_c1] at c1_cup; apply c1_cup.head?_lt_getLast? p q <;> simp; simp
    rw [eq_c2] at c2_cup; apply c2_cup.head?_lt_getLast? q r <;> simp
  · exists 1, n + 1, [p], c1, c2.dropLast, (by simp), c1_cup, c2_cup.dropLast; simp
    rw [eq_c1] at c1_in_S ⊢; rw [eq_c2] at c2_in_S ⊢
    simp only [List.getLast?_concat, List.baek_cons_in, List.baek_append_in, List.baek_nil_in, and_true,
      List.head?_cons, List.baek_getLast?_cons_append_cons, List.getLast?_singleton, true_and,
      List.dropLast_concat]
        at c1_in_S c2_in_S ⊢; ring_nf;
    simp only [List.cons_append, List.head?_cons]
    tauto
  · exists n + 1, 1, c1.tail, c2, [r], c1_cup.tail, c2_cup, (by simp); simp
    rw [eq_c1] at c1_in_S ⊢; rw [eq_c2] at c2_in_S ⊢
    simp at c1_in_S c2_in_S ⊢; tauto

theorem Config.join_n2_n3_join_n3_n2_main (S : Finset α) (n : ℕ) (cap4_free : ¬C.HasNCap 4 S)
    (cup_free : ¬C.HasNCup (n + 4) S) {cx : List α} (cx_cup : C.NCup (n + 2) cx) (cx_in_S : cx.baekIn S)
    {cx1 : List α} (cx1_cup : C.NCup (n + 3) cx1) (cx1_in_S : cx1.baekIn S) {cy1 : List α}
    (cy1_cup : C.NCup (n + 3) cy1) (cy1_in_S : cy1.baekIn S) {cy : List α} (cy_cup : C.NCup (n + 2) cy)
    (cy_in_S : cy.baekIn S) (x : α) (cx_last : x ∈ cx.getLast?) (cx1_head : x ∈ cx1.head?) (y : α)
    (cy1_last : y ∈ cy1.getLast?) (cy_head : y ∈ cy.head?) :
    ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  have l := cap4FreeLabel cap4_free
  have x_in_S := cx_in_S _ (List.mem_of_mem_getLast? cx_last)
  have y_in_S := cy_in_S _ (List.mem_of_mem_head? cy_head)
  rcases lt_or_ge y x with (hxy | hxy)
  -- Case y < x
  · by_cases lyx : l.Slope y x
    · exfalso; apply cup_free; use cy1 ++ [x]; constructor
      apply cy1_cup.extend_right lyx <;> try assumption
      simp; constructor <;> assumption
    · exfalso; apply cup_free; use y::cx1; constructor
      apply cx1_cup.extend_left lyx <;> try assumption
      simp; constructor <;> assumption
  -- Case x ≤ y
  rcases cx1_cup.take_head_last with ⟨x, cx1', z, eq_cx1, cx1'_cup⟩
  rw [eq_cx1] at cx1_head; simp at cx1_head; subst cx1_head
  rcases cy1_cup.take_head_last with ⟨w, cy1', y, eq_cy1, cy1'_cup⟩
  rw [eq_cy1] at cy1_last; simp at cy1_last; subst cy1_last
  have z_in_S : z ∈ S := by rw [eq_cx1] at cx1_in_S <;> simp at cx1_in_S <;> tauto
  have w_in_S : w ∈ S := by rw [eq_cy1] at cy1_in_S <;> simp at cy1_in_S <;> tauto
  rcases lt_trichotomy x w with (hwx | hwx | hwx); swap
  · subst hwx;
    apply
          C.join_n2_n3_n2 S cap4_free cup_free cx_cup cx_in_S cy1_cup cy1_in_S cy_cup cy_in_S x
            cx_last _ y _ cy_head <;>
        rw [eq_cy1] <;>
      simp
  · by_cases lxw : l.Slope x w
    · have cxw_cup : C.NCup (n + 3) (cx ++ [w]) := by
        apply cx_cup.extend_right lxw <;> try assumption
      apply C.join_n2_n2_interweaved cxw_cup _ cy1_cup cy1_in_S w
      simp; rw [eq_cy1]; simp; simp; tauto
    · exfalso; apply cup_free; use x::cy1; constructor
      apply cy1_cup.extend_left lxw <;> try assumption;
      rw [eq_cy1]; simp
      simp; constructor <;> assumption
  -- w < x
  rcases lt_trichotomy z y with (hyz | hyz | hyz);
  swap
  · subst hyz;
    apply
          C.join_n2_n3_n2 S cap4_free cup_free cx_cup cx_in_S cx1_cup cx1_in_S cy_cup cy_in_S x
            cx_last _ z _ cy_head <;>
        rw [eq_cx1] <;>
      simp
  · by_cases lzy : l.Slope z y
    · exfalso; apply cup_free; use cx1 ++ [y]; constructor
      apply cx1_cup.extend_right lzy <;> try assumption
      rw [eq_cx1]; simp
      simp; constructor <;> assumption
    · have zcy_cup : C.NCup (n + 3) (z::cy) := by apply cy_cup.extend_left lzy <;> try assumption
      apply C.join_n2_n2_interweaved cx1_cup _ zcy_cup _ z
      rw [eq_cx1]; simp; simp; tauto; simp; tauto
  -- y < z
  use w, x, y, z;
  refine' ⟨_, _, _⟩; tauto
  · exists 1, n + 2, [w], cy1, cy, (by simp), cy1_cup, cy_cup; simp
    constructor; tauto; constructor; ring_nf; rw [eq_cy1]; simp; assumption
  · exists n + 2, 1, cx, cx1, [z], cx_cup, cx1_cup, (by simp); simp
    constructor; tauto; constructor; rw [←Option.mem_def]; assumption
    rw [eq_cx1]; simp

theorem Config.join_n2_n3_join_n3_n2 (S : Finset α) (n : ℕ) (cap4_free : ¬C.HasNCap 4 S)
    (cup_free : ¬C.HasNCup (n + 4) S) (hx : C.HasJoin (n + 2) (n + 3) S)
    (hy : C.HasJoin (n + 3) (n + 2) S) : ∃ p q r s, C.HasInterweavedLaced (n + 3) S p q r s :=
  by
  rcases hx with ⟨x, cx, cx1, ⟨cx_cup, cx_in_S, cx_last⟩, ⟨cx1_cup, cx1_in_S, cx1_head⟩⟩
  rcases hy with ⟨y, cy1, cy, ⟨cy1_cup, cy1_in_S, cy1_last⟩, ⟨cy_cup, cy_in_S, cy_head⟩⟩
  apply
    C.join_n2_n3_join_n3_n2_main S n cap4_free cup_free cx_cup cx_in_S cx1_cup cx1_in_S cy1_cup
      cy1_in_S cy_cup cy_in_S x cx_last cx1_head y cy1_last cy_head

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Main/InductionStep.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open scoped Classical

noncomputable section

variable {α : Type _} [LinearOrder α] (C : Config α)

namespace Config

def delta (n : ℕ) (S : Finset α) : Finset α :=
  S.filter fun p => C.beta S p < n ∧ p = (S.filter fun q => C.beta S q = C.beta S p).min

theorem delta_card (n : ℕ) (S : Finset α) : (C.delta n S).card ≤ n :=
  by
  calc
    (C.delta n S).card ≤ (Finset.range n).card := by
      apply Finset.card_le_card_of_injOn (C.beta S)
      · intro a ha
        simp only [delta, Finset.mem_coe, Finset.mem_filter] at ha
        exact Finset.mem_range.mpr ha.2.1
      · intro x hx y hy hxy
        rw [delta, Finset.mem_coe, Finset.mem_filter] at hx hy
        rcases hx with ⟨x_in_S, bx_lt_n, x_min⟩
        rcases hy with ⟨y_in_S, by_lt_n, y_min⟩
        rw [← WithTop.coe_eq_coe, x_min, y_min, hxy]
    _ = n := Finset.card_range n

theorem not_mem_delta {n : ℕ} {S : Finset α} {p' : α} (h : p' ∈ S \ C.delta n S) :
    n ≤ C.beta S p' ∨ ∃ p, p ∈ C.delta n S ∧ C.beta S p = C.beta S p' ∧ p < p' :=
  by
  rw [delta, Finset.mem_sdiff, Finset.mem_filter, not_and, not_and_or] at h
  cases' h with p'_in_S aux; have h := aux p'_in_S; clear aux
  by_cases bp_n : C.beta S p' < n; swap
  · left; exact not_lt.mp bp_n
  rcases h with h | h; exact absurd bp_n h
  right
  set row := S.filter fun q => C.beta S q = C.beta S p' with def_row
  have row_nonempty : row.Nonempty := by
    use p'; rw [def_row]; rw [Finset.mem_filter]
    constructor; assumption; exact rfl
  have row_in_S : row ⊆ S := Finset.filter_subset _ _
  set p := row.min' row_nonempty with def_p
  have p_in_row : p ∈ row := Finset.min'_mem _ row_nonempty
  have bp_eq_bp' : C.beta S p = C.beta S p' :=
    by
    rw [def_row] at p_in_row; rw [Finset.mem_filter] at p_in_row
    exact p_in_row.right
  have p'_in_row : p' ∈ row := by
    rw [def_row]; rw [Finset.mem_filter]; constructor; assumption
    exact rfl
  exists p; refine' ⟨_, bp_eq_bp', _⟩
  · rw [delta]; simp only [Finset.mem_filter]
    rw [bp_eq_bp']; rw [← def_row]
    refine' ⟨row_in_S p_in_row, bp_n, _⟩
    rw [def_p]; exact Finset.coe_min' _
  · rw [← Finset.coe_min' row_nonempty] at h
    suffices p_le_p' : p ≤ p' by
      rw [le_iff_lt_or_eq] at p_le_p'
      rcases p_le_p' with p_lt_p' | p_eq_p'
      assumption; exfalso; apply h; rw [← def_p, p_eq_p']
    rw [def_p]; exact Finset.min'_le _ _ p'_in_row

theorem find_join {n : ℕ} {S : Finset α} (l : C.Label S) (cup_free : ¬C.HasNCup (n + 4) S)
    (no_join : ¬C.HasJoin (n + 3) (n + 2) S) (o p : α) (c : List α) (m : ℕ) (o_in_S : o ∈ S)
    (p_in_S : p ∈ S) (o_le_p : o ≤ p) (c_in_S : c.baekIn S) (c_ncup : C.NCup m c) (c_head : p ∈ c.head?)
    (le_m : n + 2 ≤ m) (ho : n + 2 ≤ C.beta S o) : False :=
  by
  rw [le_iff_lt_or_eq] at o_le_p; cases' o_le_p with o_lt_p o_eq_p
  · rcases C.betaCup S o_in_S with ⟨d, d_in_S, d_ncup, d_last⟩
    by_cases sop : l.Slope o p
    · apply cup_free
      have dp_ncup := d_ncup.extend_right sop o_lt_p p_in_S d_in_S d_last
      have ineq : n + 4 ≤ C.beta S o + 1 + 1 := by linarith
      apply hasNCup_le ineq; use d ++ [p]
      constructor; exact dp_ncup; simp; tauto
    · apply no_join
      rcases d_ncup.take_right_with_last (n + 3) o (by simp) (by linarith) d_last with
        ⟨d', d'_in_d, d'_ncup, d'_last⟩
      have oc_ncup := c_ncup.extend_left sop o_in_S o_lt_p c_in_S c_head
      rcases oc_ncup.take_left_with_head (n + 2) o (by simp) (by linarith) (by simp) with
        ⟨c', c'_in_oc, c'_ncup, c'_head⟩
      use o, d', c'
      have d'_in_S := List.baek_subset_in d'_in_d d_in_S
      have c'_in_S := List.baek_subset_in c'_in_oc (by simp <;> tauto)
      tauto
  · subst o_eq_p; apply no_join
    rcases C.betaCup S o_in_S with ⟨d, d_in_S, d_ncup, d_last⟩
    rcases d_ncup.take_right_with_last (n + 3) o (by simp) (by linarith) d_last with
      ⟨d', d'_in_d, d'_ncup, d'_last⟩
    rcases c_ncup.take_left_with_head (n + 2) o (by simp) (by linarith) c_head with
      ⟨c', c'_in_c, c'_ncup, c'_head⟩
    use o, d', c'
    have d'_in_S := List.baek_subset_in d'_in_d d_in_S
    have c'_in_S := List.baek_subset_in c'_in_c c_in_S
    tauto

theorem laced_extension {n : ℕ} {S D : Finset α} (l : C.Label S) (cup_free : ¬C.HasNCup (n + 4) S)
    (def_D : D = C.delta (n + 2) S) (no_join : ¬C.HasJoin (n + 3) (n + 2) S) {p' r : α}
    (p'r_laced : C.HasLaced (n + 2) (S \ D) p' r) :
    l.alpha p' = 1 ∧
      ∃ p : α, C.HasLaced (n + 3) S p r ∧ p < p' ∧ l.alpha p = 0 ∧ C.beta S p = C.beta S p' :=
  by
  rcases p'r_laced with
    ⟨a, b, cp', c, cr, cp'_cup, c_cup, cr_cup, ⟨cp'_in_SD, c_in_SD, cr_in_SD⟩, eq_ab, cp'_last,
      c_head, c_last, cr_head⟩
  have p'_in_SD := c_in_SD _ (List.mem_of_mem_head? c_head)
  have p'_in_S := Finset.sdiff_subset p'_in_SD
  have c_in_S := List.baek_in_superset Finset.sdiff_subset c_in_SD
  have cr_in_S := List.baek_in_superset Finset.sdiff_subset cr_in_SD
  rw [def_D] at p'_in_SD
  rcases C.not_mem_delta p'_in_SD with (p'_beta | ⟨p, p_in_delta, eq_p, p_lt_p'⟩)
  · exfalso; apply C.find_join l cup_free no_join p' p' c <;> try assumption <;> try simp
    simp
    simp
  have p_in_S : p ∈ S := by rw [delta, Finset.mem_filter] at p_in_delta; exact p_in_delta.left
  have ap_lt_ap' := (l.beta_eq_alpha_inc p_in_S p'_in_S eq_p).mp p_lt_p'
  have ap' : l.alpha p' = 1 :=
    by
    cases' Nat.lt_or_ge (l.alpha p') 2 with ap' ap'; linarith
    exfalso; apply cup_free
    have has_cup := l.add_alpha p'_in_S c_in_S c_cup c_head
    apply hasNCup_le _ has_cup; linarith
  have ap : l.alpha p = 0 := by linarith
  refine' ⟨ap', ⟨p, _, p_lt_p', ap, eq_p⟩⟩
  · have a_le_bp : a ≤ C.beta S p := by
      rw [eq_p]
      -- Take the head o' of cp'
      have cp'_nnil : cp' ≠ [] := by intro h; subst h; simp at cp'_last
      rcases List.baek_takeHead cp'_nnil with ⟨o', cp'', eq_cp'⟩
      have o'_le_p' : o' ≤ p' :=
        cp'_cup.head?_le_getLast? o' p' (by rw [eq_cp'] <;> simp) (by assumption)
      have o'_in_SD : o' ∈ S \ D := by apply cp'_in_SD <;> rw [eq_cp'] <;> simp
      have o'_in_S : o' ∈ S := Finset.sdiff_subset o'_in_SD
      rw [def_D] at o'_in_SD
      -- Locate o in delta having the same row as o'
      rcases C.not_mem_delta o'_in_SD with (le_beta | ⟨o, o_in_delta, eq_o, o_lt_o'⟩)
      · exfalso; apply C.find_join l cup_free no_join o' p' c <;> try assumption <;> try simp
        simp
      have o_in_S : o ∈ S := by
        rw [Config.delta] at o_in_delta <;> exact Finset.mem_of_mem_filter _ o_in_delta
      -- Show that the slope of o and o' is ff
      by_cases soo' : l.Slope o o'
      · have inc := slope_tt_inc_beta soo' o_in_S o'_in_S o_lt_o'
        rw [eq_o] at inc; simp at inc
      -- extend cp' to left with o
      have cp'_in_S := List.baek_in_superset Finset.sdiff_subset cp'_in_SD
      have ocp'_cup : C.NCup (a + 1) (o::cp') :=
        by
        apply cp'_cup.extend_left soo' <;> try assumption
        rw [eq_cp']; simp
      apply Nat.le_of_add_le_add_right; rw [← ocp'_cup.right]
      apply C.cup_length_le_beta
      simp; constructor <;> assumption; exact ocp'_cup.left
      apply List.mem_getLast?_cons; assumption
    rw [Config.HasLaced]
    rcases C.betaCup S p_in_S with ⟨cp, cp_in_S, cp_cup, cp_last⟩
    rcases cp_cup.take_right_with_last (a + 1) p (by simp) (by linarith) cp_last with
      ⟨dp, dp_in_cp, dp_cup, dp_last⟩
    have dp_in_S : dp.baekIn S := List.baek_subset_in dp_in_cp cp_in_S
    have spp' : ¬l.Slope p p' := by
      intro spp'
      have ineq := slope_tt_inc_beta spp' p_in_S p'_in_S p_lt_p'; linarith
    have pc_cup := c_cup.extend_left spp' p_in_S p_lt_p' c_in_S c_head
    use a + 1, b, dp, p::c, cr, dp_cup, pc_cup, cr_cup
    refine'
        ⟨⟨_, by simp <;> tauto, _⟩, by linarith, _, by simp, List.mem_getLast?_cons c_last, _⟩ <;>
      assumption

theorem main_induction_wlog (n : ℕ) : C.MainGoal n → C.MainGoalWlog (n + 1) :=
  by
  intro ih S no_join S_card cap4_free cup_free
  have l : C.Label S := cap4FreeLabel cap4_free
  set D := C.delta (n + 2) S with def_D
  have D_card := C.delta_card (n + 2) S; rw [← def_D] at D_card
  have SD_card : (n + 2).choose 2 + 2 ≤ (S \ D).card :=
    by
    apply Nat.le_of_add_le_add_right
    rw [Finset.card_sdiff_add_card]
    apply le_trans _ (Finset.card_le_card Finset.subset_union_left)
    apply le_trans _ S_card
    apply le_trans (Nat.add_le_add_left D_card _) _
    rw [Nat.add_right_comm]; apply le_of_eq
    rw [Nat.add_right_comm n 1 2]; simp; apply symm; rw [Nat.choose]; simp
    rw [Nat.add_comm]
  have t := ih (S \ D) SD_card ?_ ?_
  swap;
  · intro h; rcases h with ⟨c, ⟨_, c_in⟩⟩
    apply cap4_free; use c; constructor; assumption
    apply List.baek_in_superset _ c_in; exact Finset.sdiff_subset
  swap;
  · intro h; rcases h with ⟨c, ⟨c_cup, c_in⟩⟩
    rcases c_cup.cons_head_tail with ⟨p, c', eq_c, -⟩
    have p_in_c : p ∈ c := by rw [eq_c] <;> left <;> exact rfl
    have p_in_SD : p ∈ S \ D := c_in _ p_in_c
    rw [def_D] at p_in_SD
    have p_in_S : p ∈ S := Finset.sdiff_subset p_in_SD
    have c_in_S : c.baekIn S := fun a ha => Finset.sdiff_subset (c_in a ha)
    rcases C.not_mem_delta p_in_SD with (le_bp | ⟨o, o_in_delta, bo_eq_bp, o_lt_p⟩)
    · apply C.find_join l cup_free no_join p p c <;> try assumption <;> try simp
      simp
      rw [eq_c]; simp
      simp
    · have o_in_S : o ∈ S := by
        rw [delta, Finset.mem_filter] at o_in_delta
        exact o_in_delta.left
      have ao_lt_ap := (l.beta_eq_alpha_inc o_in_S p_in_S bo_eq_bp).mp o_lt_p
      have has_cup := l.add_alpha p_in_S c_in_S c_cup (by rw [eq_c] <;> simp)
      apply cup_free; ring_nf at has_cup ⊢
      apply hasNCup_le _ has_cup; linarith
  · rcases t with ⟨p', q', r, s, ⟨⟨p'_lt_q', q'_le_r, r_lt_s⟩, ⟨p'r_laced, q's_laced⟩⟩⟩
    rcases C.laced_extension l cup_free def_D no_join p'r_laced with
      ⟨ap', ⟨p, pr_laced, p_lt_p', ap, bp⟩⟩
    rcases C.laced_extension l cup_free def_D no_join q's_laced with
      ⟨aq', ⟨q, qs_laced, q_lt_q', aq, bq⟩⟩
    rcases pr_laced.mem_ends with ⟨p_in_S, r_in_S⟩
    rcases qs_laced.mem_ends with ⟨q_in_S, s_in_S⟩
    have p'_in_S := Finset.sdiff_subset p'r_laced.mem_ends.left
    have q'_in_S := Finset.sdiff_subset q's_laced.mem_ends.left
    refine' ⟨p, q, r, s, ⟨⟨_, _, r_lt_s⟩, pr_laced, qs_laced⟩⟩
    · have ap_eq_aq := Eq.trans ap aq.symm
      rw [C.alpha_eq_beta_inc p_in_S q_in_S ap_eq_aq]
      rw [bp, bq]
      have ap'_eq_aq' := Eq.trans ap' aq'.symm
      rw [← C.alpha_eq_beta_inc p'_in_S q'_in_S ap'_eq_aq']
      exact p'_lt_q'
    · apply le_of_lt
      exact lt_of_lt_of_le q_lt_q' q'_le_r

end Config
end

end
end ErdosSzekeres.Baek

/- Ported from J. Baek, jcpaik/erdos-tuza-valtr at commit
a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f, Apache License 2.0.
Original file: ErdosTuzaValtr/Main/Main.lean.
Modified for Lean 4.29.1; scoped within this node. -/
namespace ErdosSzekeres.Baek
section
open List

open scoped Classical

noncomputable section

variable {γ : Type _} [LinearOrder γ] (C : Config γ)

open OrderDual

theorem Config.BaekMirror_mainGoal (n : ℕ) : C.MainGoal n → C.BaekMirror.MainGoal n :=
  by
  intro h Sm hSm cap4_free cup_free
  have eq_S : Sm.ofBaekMirror.BaekMirror = Sm := Finset.ofBaekMirrorBaekMirror
  rw [← eq_S] at hSm cap4_free cup_free ⊢
  set S := Sm.ofBaekMirror
  rw [Finset.BaekMirror_card] at hSm
  rw [BaekMirror.hasNCap] at cap4_free
  rw [BaekMirror.hasNCup] at cup_free
  have goal := h S hSm cap4_free cup_free
  rcases goal with ⟨p, q, r, s, interweave⟩
  exists toDual s, toDual r, toDual q, toDual p
  rw [BaekMirror.hasInterweavedLaced]
  exact interweave

theorem Config.main_lemma (n : ℕ) : C.MainGoal n :=
  by
  induction' n with n ih
  · intro S hS cap4_free cup_free; simp at hS
    set Sl := S.sort (· ≤ ·) with def_Sl
    have Sl_card : 3 ≤ Sl.length := by rw [def_Sl] <;> simp <;> exact hS
    have mem_Sl : ∀ {a : γ}, a ∈ Sl ↔ a ∈ S := by
      intro a; rw [def_Sl];
      exact Finset.mem_sort (· ≤ ·)
    -- Take three elements of S
    rcases List.baek_takeHead3 Sl_card with ⟨a, b, c, Sl', eq_Sl⟩
    have abc_mem : a ∈ S ∧ b ∈ S ∧ c ∈ S := by
      rw [← mem_Sl, ← mem_Sl, ← mem_Sl] <;> rw [eq_Sl] <;> simp
    have abc_lt : a < b ∧ b < c := by
      have sorted := (Finset.sortedLT_sort S).pairwise
      rw [← def_Sl, eq_Sl] at sorted
      simp at sorted; tauto
    refine' ⟨a, b, b, c, _, ⟨_, _⟩⟩
    exact ⟨abc_lt.left, le_refl b, abc_lt.right⟩
    use 1, 1, [a], [a, b], [b]; simp; tauto
    use 1, 1, [b], [b, c], [c]; simp; tauto
  · intro S hS cap4_free cup_free
    by_cases join_n3_n2 : C.HasJoin (n + 3) (n + 2) S; swap
    · apply C.main_induction_wlog <;> assumption
    by_cases join_n2_n3 : C.HasJoin (n + 2) (n + 3) S; swap
    · rw [← Finset.BaekMirror_card] at hS
      rw [← BaekMirror.hasJoin] at join_n2_n3
      rw [← BaekMirror.hasNCap] at cap4_free
      rw [← BaekMirror.hasNCup] at cup_free
      have BaekMirrored_goal :=
        C.BaekMirror.main_induction_wlog n (C.BaekMirror_mainGoal n ih) S.BaekMirror join_n2_n3 hS cap4_free
          cup_free
      rcases BaekMirrored_goal with ⟨sm, rm, qm, pm, mgoal⟩
      have eq_p := pm.toDual_ofDual; set p := ofDual pm
      have eq_q := qm.toDual_ofDual; set q := ofDual qm
      have eq_r := rm.toDual_ofDual; set r := ofDual rm
      have eq_s := sm.toDual_ofDual; set s := ofDual sm
      exists p, q, r, s
      rw [← eq_p, ← eq_q, ← eq_r, ← eq_s, BaekMirror.hasInterweavedLaced] at mgoal
      assumption
    apply C.join_n2_n3_join_n3_n2 <;> assumption

theorem main (n : ℕ) (C : Config γ) (S : Finset γ) (hS : Nat.choose (n + 2) 2 + 2 ≤ S.card) :
    C.HasNCap 4 S ∨ C.HasNGon (n + 3) S :=
  by
  by_cases has_cap4 : C.HasNCap 4 S; left; exact has_cap4
  by_cases has_cup : C.HasNCup (n + 3) S
  · right; apply ncup_is_ngon _ has_cup; simp
  rcases C.main_lemma n S hS has_cap4 has_cup with ⟨p, q, r, s, laced⟩
  right; exact C.hasInterweavedLaced_hasNGon has_cap4 laced
end

end
end ErdosSzekeres.Baek




namespace ErdosSzekeres

private theorem baek_all_triples_of_consecutive
    {n m : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (f : Fin m ↪o Fin n) (hone : OneChangeOn χ s) (hmem : ∀ i, f i ∈ s)
    (c : Turn)
    (hlocal : ∀ (i j k : Fin m), (hij : i < j) → (hjk : j < k) →
      j.val = i.val + 1 → k.val = j.val + 1 →
      χ ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩ = c) :
    IsMonochromaticChain χ c f := by
  have aux : ∀ span : ℕ, ∀ (i j k : Fin m), k.val - i.val = span →
      (hij : i < j) → (hjk : j < k) →
      χ ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩ = c := by
    intro span
    induction span using Nat.strong_induction_on with
    | h span ih =>
      intro i j k hspan hij hjk
      by_cases hijSucc : j.val = i.val + 1
      · by_cases hjkSucc : k.val = j.val + 1
        · exact hlocal i j k hij hjk hijSucc hjkSucc
        · let q : Fin m := ⟨k.val - 1, by omega⟩
          have hjq : j < q := by change j.val < k.val - 1; omega
          have hqk : q < k := by change k.val - 1 < k.val; omega
          have ha := ih (q.val - i.val) (by dsimp [q]; omega) i j q rfl hij hjq
          have hd := ih (k.val - j.val) (by omega) j q k rfl hjq hqk
          have hall := (hone (f.strictMono hij) (f.strictMono hjq)
            (f.strictMono hqk) (hmem i) (hmem j) (hmem q) (hmem k)).all_eq_of_outer_eq
            (ha.trans hd.symm)
          exact hall.1.symm.trans ha
      · let q : Fin m := ⟨j.val - 1, by omega⟩
        have hiq : i < q := by change i.val < j.val - 1; omega
        have hqj : q < j := by change j.val - 1 < j.val; omega
        have ha := ih (j.val - i.val) (by omega) i q j rfl hiq hqj
        have hd := ih (k.val - q.val) (by dsimp [q]; omega) q j k rfl hqj hjk
        have hall := (hone (f.strictMono hiq) (f.strictMono hqj)
          (f.strictMono hjk) (hmem i) (hmem q) (hmem j) (hmem k)).all_eq_of_outer_eq
          (ha.trans hd.symm)
        exact hall.2.1.symm.trans (hall.1.symm.trans ha)
  exact ⟨f.strictMono, fun i j k hij hjk ↦ aux _ i j k rfl hij hjk⟩

private theorem baek_chain3_iff_consecutive {α : Type*} {R : α → α → α → Prop}
    {a b : α} {l : List α} :
    List.BaekChain3 R a b l ↔ CupCap.Consecutive R a b l := by
  induction l generalizing a b with
  | nil => simp
  | cons x xs ih => simp only [List.chain3_cons, CupCap.consecutive_cons, ih]

private theorem baek_chain3'_iff_consecutive' {α : Type*} {R : α → α → α → Prop}
    {l : List α} : List.BaekChain3' R l ↔ CupCap.Consecutive' R l := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l => exact baek_chain3_iff_consecutive

private theorem baek_mono_set_of_chain3
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {l : List (Fin n)}
    {R : Fin n → Fin n → Fin n → Prop} (c : Turn)
    (hone : OneChangeOn χ s) (hmem : l.baekIn s)
    (horder : l.IsChain (· < ·)) (hchain : List.BaekChain3' R l)
    (hrel : ∀ a b d, (hab : a < b) → (hbd : b < d) →
      R a b d → χ ⟨a, b, d, hab, hbd⟩ = c) :
    ∀ t : OrderedTriple n, t.i ∈ l.toFinset → t.j ∈ l.toFinset →
      t.k ∈ l.toFinset → χ t = c := by
  let f : Fin l.length ↪o Fin n :=
    OrderEmbedding.ofStrictMono l.get horder.sortedLT.strictMono_get
  have hmono : IsMonochromaticChain χ c f := by
    apply baek_all_triples_of_consecutive f hone (fun i ↦ hmem _ (l.get_mem i)) c
    intro i j k hij hjk hjval hkval
    have hkval' : k.val = i.val + 2 := by omega
    have hget := CupCap.consecutive'_getElem
      (baek_chain3'_iff_consecutive'.mp hchain) i.val (by omega)
    apply hrel (f i) (f j) (f k) (f.strictMono hij) (f.strictMono hjk)
    simpa [f, List.get_eq_getElem, hjval, hkval'] using hget
  have himage : Finset.univ.image f = l.toFinset := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
    change (∃ i, l.get i = x) ↔ x ∈ l
    exact List.mem_iff_get.symm
  rw [← himage]
  exact FinsetPolygon.IsMonochromaticChain.isMonochromaticSet_image hmono

private def baek_config {n : ℕ} (χ : TripleColoring n) : Baek.Config (Fin n) where
  Cup3 a b c := CupCap.totalColor χ a b c = Turn.left
  DecidableCup3 a b c := inferInstance

private theorem baek_cup_isCupSet {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} {l : List (Fin n)} (hone : OneChangeOn χ s)
    (hmem : l.baekIn s) (hcup : (baek_config χ).Cup l) : IsCupSet χ l.toFinset := by
  apply baek_mono_set_of_chain3 Turn.left hone hmem hcup.1 hcup.2
  intro a b c hab hbc h
  simpa [baek_config, CupCap.totalColor_of_lt χ hab hbc] using h

private theorem baek_cap_isCapSet {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} {l : List (Fin n)} (hone : OneChangeOn χ s)
    (hmem : l.baekIn s) (hcap : (baek_config χ).Cap l) : IsCapSet χ l.toFinset := by
  apply baek_mono_set_of_chain3 Turn.right hone hmem hcap.1 hcap.2
  intro a b c hab hbc h
  have hne : χ ⟨a, b, c, hab, hbc⟩ ≠ Turn.left := by
    simpa [baek_config, Baek.Config.Cap3, CupCap.totalColor_of_lt χ hab hbc] using h
  cases hcol : χ ⟨a, b, c, hab, hbc⟩ <;> simp_all


private theorem baek_cup_insert_apex_isStrong
    {n : ℕ} {χ : TripleColoring n} {cup : Finset (Fin n)} {p q r : Fin n}
    (hone : OneChangeOn χ (insert q cup)) (hcup : IsCupSet χ cup)
    (hp : p ∈ cup) (hr : r ∈ cup) (hpq : p < q) (hqr : q < r)
    (hmin : ∀ x ∈ cup, p ≤ x) (hmax : ∀ x ∈ cup, x ≤ r)
    (hcap : χ ⟨p, q, r, hpq, hqr⟩ = Turn.right) :
    IsStrongPolygonSet χ (insert q cup) := by
  have hqnot : q ∉ cup := by
    intro hq
    have h := hcup ⟨p, q, r, hpq, hqr⟩ hp hq hr
    rw [hcap] at h
    cases h
  have hmid : ∀ x ∈ cup, ∀ y ∈ cup, (hxq : x < q) → (hqy : q < y) →
      χ ⟨x, q, y, hxq, hqy⟩ = Turn.right := by
    intro x hx y hy hxq hqy
    have hpqy : χ ⟨p, q, y, hpq, hqy⟩ = Turn.right := by
      by_cases hyr : y = r
      · subst y
        exact hcap
      have hyr : y < r := lt_of_le_of_ne (hmax y hy) hyr
      have hleft := hcup ⟨p, y, r, hpq.trans hqy, hyr⟩ hp hy hr
      have hallow := hone hpq hqy hyr (by simp [hp]) (by simp)
        (by simp [hy]) (by simp [hr])
      rcases hallow with h | h | h | h | h | h | h | h <;> simp_all
    by_cases hpx : p = x
    · subst x
      exact hpqy
    have hpx : p < x := lt_of_le_of_ne (hmin x hx) hpx
    have hleft := hcup ⟨p, x, y, hpx, hxq.trans hqy⟩ hp hx hy
    have hallow := hone hpx hxq hqy (by simp [hp]) (by simp [hx])
      (by simp) (by simp [hy])
    rcases hallow with h | h | h | h | h | h | h | h <;> simp_all
  have hcolor : ∀ t : OrderedTriple n, t.i ∈ insert q cup →
      t.j ∈ insert q cup → t.k ∈ insert q cup →
      χ t = if t.j = q then Turn.right else Turn.left := by
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert] at hi hj hk
    rcases hi with rfl | hi
    · simp only [ne_of_gt hij, if_false]
      have hj : j ∈ cup := hj.resolve_left (ne_of_gt hij)
      have hk : k ∈ cup := hk.resolve_left (ne_of_gt (hij.trans hjk))
      have hpj := hpq.trans hij
      have hfirst := hmid p hp j hj hpq hij
      have hsecond := hmid p hp k hk hpq (hij.trans hjk)
      have hleft := hcup ⟨p, j, k, hpj, hjk⟩ hp hj hk
      have hallow := hone hpq hij hjk (by simp [hp]) (by simp)
        (by simp [hj]) (by simp [hk])
      rcases hallow with h | h | h | h | h | h | h | h <;> simp_all
    rcases hj with rfl | hj
    · simpa using hmid i hi k (hk.resolve_left (ne_of_gt hjk)) hij hjk
    rcases hk with rfl | hk
    · simp only [ne_of_lt hjk, if_false]
      have hiq := hij.trans hjk
      have hfirst := hmid i hi r hr hiq hqr
      have hsecond := hmid j hj r hr hjk hqr
      have hleft := hcup ⟨i, j, r, hij, hjk.trans hqr⟩ hi hj hr
      have hallow := hone hij hjk hqr (by simp [hi]) (by simp [hj])
        (by simp) (by simp [hr])
      rcases hallow with h | h | h | h | h | h | h | h <;> simp_all
    have hjq : j ≠ q := by intro h; subst j; exact hqnot hj
    simpa [hjq] using hcup ⟨i, j, k, hij, hjk⟩ hi hj hk
  intro i j k l hij hjk hkl hi hj hk hl
  constructor
  · rw [hcolor _ hi hj hk, hcolor _ hi hj hl]
  · rw [hcolor _ hi hk hl, hcolor _ hj hk hl]


/-- Baek single-set bound: a one-change finite set with no four-cap and no strong k-set has at most one plus choose (k-1) two vertices, for k at least three. Port of J. Baek, On the Erdos-Tuza-Valtr conjecture, Theorem 2.7, Apache-2.0 source jcpaik/erdos-tuza-valtr at a5ad53e.
@node
@ws C
@kind formalization
@dangling-ok Approved R21 input to decomposableStateUpper_four_diagonal_of_gates, registered after this node is closed. -/
theorem card_le_choose_of_oneChange_no_capFour_no_strong {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} (hk : 3 ≤ k) (hone : OneChangeOn χ s) (hnoCap : ¬ContainsCapSet χ s 4) (hnoStrong : ¬ContainsStrongPolygonSet χ s k) : s.card ≤ 1 + Nat.choose (k - 1) 2 := by
  classical
  have hnoBaekCap : ¬(baek_config χ).HasNCap 4 s := by
    rintro ⟨capList, ⟨hcap, hlength⟩, hmem⟩
    apply hnoCap
    refine ⟨capList.toFinset, ?_, ?_, baek_cap_isCapSet hone hmem hcap⟩
    · intro x hx
      exact hmem x (List.mem_toFinset.mp hx)
    · exact (List.toFinset_card_of_nodup
        (List.isChain_iff_pairwise.mp hcap.1).nodup).trans hlength
  by_contra hbound
  have hindex : k - 3 + 3 = k := by omega
  have hchoose : k - 3 + 2 = k - 1 := by omega
  rcases Baek.main (k - 3) (baek_config χ) s (by rw [hchoose]; omega) with hcap | hgon
  · exact hnoBaekCap hcap
  rw [hindex] at hgon
  obtain ⟨capList, cupList, ⟨hgon, hsum⟩, hcapMem, hcupMem⟩ := hgon
  rcases hgon with ⟨hcapLen, hcap, hcupLen, hcup, hhead, hlast⟩
  have hcapBound : capList.length ≤ 3 := by
    by_contra hlength
    have hfour : 4 ≤ capList.length := by omega
    apply hnoBaekCap
    refine ⟨capList.take 4, ⟨⟨hcap.1.take 4, hcap.2.take 4⟩, ?_⟩, ?_⟩
    · simpa using hfour
    · intro x hx
      exact hcapMem x (List.take_subset _ _ hx)
  have hcupSub : cupList.toFinset ⊆ s := by
    intro x hx
    exact hcupMem x (List.mem_toFinset.mp hx)
  have hcupSet : IsCupSet χ cupList.toFinset := baek_cup_isCupSet hone hcupMem hcup
  have hcupCard : cupList.toFinset.card = cupList.length :=
    List.toFinset_card_of_nodup (List.isChain_iff_pairwise.mp hcup.1).nodup
  obtain ⟨p, q, tail, hcapEq⟩ := List.baek_takeHead2 hcapLen
  subst capList
  cases tail with
  | nil =>
    apply hnoStrong
    refine ⟨cupList.toFinset, hcupSub, ?_,
      FinsetPolygon.IsCupSet.isStrongPolygonSet hcupSet⟩
    rw [hcupCard]
    simp only [List.length_cons, List.length_nil] at hsum
    omega
  | cons r tail =>
    have htail : tail = [] := by
      simp only [List.length_cons] at hcapBound
      have hlength : tail.length = 0 := by omega
      simpa using hlength
    subst tail
    have horder : p < q ∧ q < r := by simpa using hcap.1
    have hpq := horder.1
    have hqr := horder.2
    have hcapSet := baek_cap_isCapSet hone hcapMem hcap
    have hcapTurn : χ ⟨p, q, r, hpq, hqr⟩ = Turn.right :=
      hcapSet _ (by simp) (by simp) (by simp)
    have hpHead : p ∈ cupList.head? := by
      simpa [Option.mem_def] using hhead.symm
    have hrLast : r ∈ cupList.getLast? := by
      simpa [Option.mem_def] using hlast.symm
    have hpCup : p ∈ cupList.toFinset :=
      List.mem_toFinset.mpr (List.mem_of_mem_head? hpHead)
    have hrCup : r ∈ cupList.toFinset :=
      List.mem_toFinset.mpr (List.mem_of_mem_getLast? hrLast)
    have hmin : ∀ x ∈ cupList.toFinset, p ≤ x := by
      intro x hx
      obtain ⟨rest, hEq⟩ := List.baek_takeHead' hpHead
      have hpair := List.isChain_iff_pairwise.mp hcup.1
      rw [hEq] at hpair hx
      simp only [List.pairwise_cons] at hpair
      simp only [List.mem_toFinset, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_rfl
      · exact (hpair.1 x hx).le
    have hmax : ∀ x ∈ cupList.toFinset, x ≤ r := by
      intro x hx
      obtain ⟨rest, hEq⟩ := List.baek_takeLast' hrLast
      have hpair := List.isChain_iff_pairwise.mp hcup.1
      rw [hEq] at hpair hx
      simp only [List.pairwise_append] at hpair
      simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact (hpair.2.2 x hx r (by simp)).le
      · exact le_rfl
    have hqMem : q ∈ s := hcapMem q (by simp)
    have hsub : insert q cupList.toFinset ⊆ s := by
      simpa using Finset.insert_subset_iff.mpr ⟨hqMem, hcupSub⟩
    have hstrong := baek_cup_insert_apex_isStrong (hone.mono hsub) hcupSet
      hpCup hrCup hpq hqr hmin hmax hcapTurn
    have hqNot : q ∉ cupList.toFinset := by
      intro hq
      have h := hcupSet ⟨p, q, r, hpq, hqr⟩ hpCup hq hrCup
      rw [hcapTurn] at h
      cases h
    apply hnoStrong
    refine ⟨insert q cupList.toFinset, hsub, ?_, hstrong⟩
    rw [Finset.card_insert_of_notMem hqNot, hcupCard]
    simp only [List.length_cons, List.length_nil] at hsum
    omega


end ErdosSzekeres
