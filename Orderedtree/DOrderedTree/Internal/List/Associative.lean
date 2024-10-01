/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Data.DHashMap.Internal.List.Associative

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

theorem Ordering.eq_eq_of_isLE_of_isLE_swap {o : Ordering} : o.isLE → o.swap.isLE → o = .eq := by
  cases o <;> simp [isLE, swap]

theorem Ordering.eq_eq_of_eq_swap {o : Ordering} : o = o.swap → o = .eq := by
  cases o <;> simp [swap]

@[simp]
theorem Ordering.isLE_eq_false {o : Ordering} : o.isLE = false ↔ o = gt := by
  cases o <;> simp [isLE]

@[simp]
theorem Ordering.swap_eq_gt {o : Ordering} : o.swap = .gt ↔ o = .lt := by
  cases o <;> simp [swap]

theorem Ordering.isLE_iff_eq_lt_or_eq_eq {o : Ordering} : o.isLE ↔ o = .lt ∨ o = .eq := by
  cases o <;> simp [isLE]

theorem Ordering.isLE_of_eq_lt {o : Ordering} : o = .lt → o.isLE := by
  rintro rfl; rfl

theorem Ordering.eq_one {o : Ordering} : o = .lt ∨ o = .gt ∨ o = .eq := by
  cases o <;> simp

-- https://github.com/leanprover/lean4/issues/5295
instance : LawfulBEq Ordering where
  eq_of_beq {a b} := by cases a <;> cases b <;> simp <;> rfl
  rfl {a} := by cases a <;> rfl

theorem LawfulBEq.beq_eq_eq {α : Type u} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · cases h : a == b
    · simpa
    · simpa using eq_of_beq h

variable {α : Type u} {β : α → Type v}

/-- More usable version of `List.minimum?`. This one is not tail-recursive, which is fine because you're not supposed to execute it. -/
def min? [Min α] : List α → Option α
  | [] => none
  | (x::xs) => min (some x) (min? xs)

theorem min?_nil [Min α] : min? ([] : List α) = none := rfl
theorem min?_cons [Min α] {x : α} {xs : List α} : min? (x::xs) = min (some x) (min? xs) := rfl

variable [Ord α]

/-- `a == b` is defined as `compare a b == .eq`. -/
def beqOfOrd : BEq α where
  beq a b := compare a b == .eq

attribute [local instance] leOfOrd ltOfOrd beqOfOrd

theorem le_iff {a b : α} : a ≤ b ↔ (compare a b).isLE := Iff.refl _
theorem lt_iff {a b : α} : a < b ↔ compare a b = .lt := Iff.refl _
theorem beq_eq {a b : α} : (a == b) = (compare a b == .eq) := rfl
theorem beq_iff {a b : α} : (a == b) ↔ compare a b = .eq := by
  rw [beq_eq, beq_iff_eq]

theorem le_of_lt {a b : α} : a < b → a ≤ b := by
  rw [le_iff, lt_iff]
  exact Ordering.isLE_of_eq_lt

theorem le_iff_lt_or_beq {a b : α} : a ≤ b ↔ a < b ∨ a == b := by
  simpa [le_iff, lt_iff, beq_iff] using Ordering.isLE_iff_eq_lt_or_eq_eq

theorem le_of_beq {a b : α} (h : a == b) : a ≤ b :=
  le_iff_lt_or_beq.2 <| Or.inr h

theorem not_lt_of_beq {a b : α} : a == b → ¬a < b := by
  simp only [beq_iff, lt_iff]
  cases compare a b <;> simp

theorem beq_eq_false_of_lt {a b : α} : a < b → (a == b) = false := by
  simp only [beq_eq, lt_iff]
  cases compare a b <;> simp

/-- Class for "oriented" ordering functions. -/
class OrientedOrd (α : Type u) [Ord α] where
  /-- Swapping the arguments to `compare` swaps the result. -/
  eq_swap {a b : α} : compare a b = (compare b a).swap

theorem lt_or_lt_or_beq [OrientedOrd α] (a b : α) : a < b ∨ b < a ∨ a == b := by
  simp only [le_iff, lt_iff, beq_eq]
  rw [OrientedOrd.eq_swap (a := b) (b := a)]
  cases compare a b <;> simp [Ordering.swap]

@[simp]
theorem compare_self [OrientedOrd α] {a : α} : compare a a = .eq := by
  apply Ordering.eq_eq_of_eq_swap
  exact OrientedOrd.eq_swap

theorem beq_refl [OrientedOrd α] {a : α} : a == a := by
  simp [beq_iff]

theorem beq_symm [OrientedOrd α] {a b : α} (h : a == b) : b == a := by
  rw [beq_iff] at h
  rw [beq_iff, OrientedOrd.eq_swap, h, Ordering.swap]

theorem beq_comm [OrientedOrd α] (a b : α) : (a == b) = (b == a) := by
  rw [beq_eq, beq_eq, OrientedOrd.eq_swap]
  cases compare b a <;> simp [Ordering.swap, Bool.beq_eq_decide_eq]

theorem irrefl [OrientedOrd α] {a b : α} : a ≤ b → b ≤ a → a == b := by
  rw [le_iff, le_iff, beq_iff, OrientedOrd.eq_swap (a := b)]
  exact Ordering.eq_eq_of_isLE_of_isLE_swap

theorem not_lt_self [OrientedOrd α] {a : α} : ¬a < a := by
  simp [lt_iff]

theorem not_le_iff_lt [OrientedOrd α] {a b : α} : ¬a ≤ b ↔ b < a := by
  simp [le_iff, lt_iff, OrientedOrd.eq_swap (a := a)]

theorem not_lt_iff_le [OrientedOrd α] {a b : α} : ¬a < b ↔ b ≤ a :=
  Decidable.not_iff_comm.1 not_le_iff_lt

/-- Class for transitive ordering functions. -/
class TransOrd (α : Type u) [Ord α] extends OrientedOrd α where
  /-- ≤ is transitive. -/
  le_trans {a b c : α} : (compare a b).isLE → (compare b c).isLE → (compare a c).isLE

theorem le_trans [TransOrd α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff] using TransOrd.le_trans

theorem lt_of_lt_of_beq [TransOrd α] {a b c : α} (h₁ : a < b) (h₂ : b == c) : a < c := by
  rw [← not_le_iff_lt]
  intro h₃
  have := not_lt_iff_le.2 (le_trans (le_of_beq h₂) h₃)
  contradiction

theorem lt_of_beq_of_lt [TransOrd α] {a b c : α} (h₁ : a == b) (h₂ : b < c) : a < c := by
  rw [← not_le_iff_lt]
  intro h₃
  have := not_lt_iff_le.2 (le_trans h₃ (le_of_beq h₁))
  contradiction

theorem lt_trans [TransOrd α] {a b c : α} : a < b → b < c → a < c := by
  intro hab hbc
  rcases lt_or_lt_or_beq a c with (h|h|h)
  · exact h
  · have := not_lt_iff_le.2 (le_trans (le_of_lt hbc) (le_of_lt h))
    contradiction
  · have := not_lt_iff_le.2 (le_of_lt (lt_of_lt_of_beq hbc (beq_symm h)))
    contradiction

theorem beq_trans [TransOrd α] {a b c : α} (h₁ : a == b) (h₂ : b == c) : a == c := by
  rcases lt_or_lt_or_beq a c with (h|h|h)
  · rw [beq_eq_false_of_lt (lt_of_lt_of_beq h (beq_symm h₂))] at h₁
    contradiction
  · rw [beq_comm, beq_eq_false_of_lt (lt_of_beq_of_lt h₂ h)] at h₁
    contradiction
  · exact h

theorem lt_of_le_of_lt [TransOrd α] {a b c : α} : a ≤ b → b < c → a < c := by
  intros hab hbc
  rcases le_iff_lt_or_beq.1 hab with (hab|hab)
  · exact lt_trans hab hbc
  . exact lt_of_beq_of_lt hab hbc

theorem lt_of_lt_of_le [TransOrd α] {a b c : α} : a < b → b ≤ c → a < c := by
  intros hab hbc
  rcases le_iff_lt_or_beq.1 hbc with (hbc|hbc)
  · exact lt_trans hab hbc
  · exact lt_of_lt_of_beq hab hbc

local instance : Max α where
  max a b := if a ≤ b then b else a

local instance : Min α where
  min a b := if a ≤ b then a else b

local instance : Min ((a : α) × β a) where
  min a b := if a.1 ≤ b.1 then a else b

namespace Std.DHashMap.Internal.List

/-- The smallest element of `xs` that is not less than `k`. -/
def lowerBound? (xs : List ((a : α) × β a)) (k : α) : Option ((a : α) × β a) :=
  xs.filter (fun p => k ≤ p.1) |> min?

/-- The smallest element of `xs` that is greater than `k`. -/
def upperBound? (xs : List ((a : α) × β a)) (k : α) : Option ((a : α) × β a) :=
  xs.filter (fun p => p.1 < k) |> min?

@[simp]
theorem lowerBound?_nil {k : α} : lowerBound? ([] : List ((a : α) × β a)) k = none := rfl

theorem lowerBound?_cons [TransOrd α] (l : List ((a : α) × β a)) (k : α) (v : β k) (a : α) :
    lowerBound? (⟨k, v⟩ :: l) a =
      if k < a then lowerBound? l a else min (some ⟨k, v⟩) (lowerBound? l a) := by
  rw [lowerBound?, List.filter_cons]
  simp only [decide_eq_true_eq]
  split
  · rw [min?_cons]
    split
    · exact False.elim (not_lt_self (lt_of_le_of_lt (b := k) ‹_› ‹_›))
    · rfl
  · next h =>
    rw [not_le_iff_lt] at h
    simp [h, lowerBound?]

theorem lowerBound?_insertEntry [TransOrd α] (xs : List ((a : α) × β a)) (k : α) (v : β k) (a : α) :
    lowerBound? (insertEntry k v xs) a =
      if k ≤ a then lowerBound? xs a else min (lowerBound? xs a) (some ⟨k, v⟩) := by
  sorry

end Std.DHashMap.Internal.List