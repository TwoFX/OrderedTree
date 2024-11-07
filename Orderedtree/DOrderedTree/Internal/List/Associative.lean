/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Data.DHashMap.Internal.List.Associative

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

theorem Option.unattach_eq_some {α : Type u} {p : α → Prop} {a : α} {o : Option { x // p x}} : o.unattach = some a ↔ ∃ h : p a, o = some ⟨a, h⟩ :=
  o.rec (by simp) (fun h => ⟨by simp only [unattach_some, some.injEq]; rintro rfl; exact ⟨h.2, rfl⟩,
    by simp only [some.injEq, unattach_some, forall_exists_index]; rintro hx rfl; rfl⟩)

-- unused
theorem List.min?_mem₂ {α : Type u} [Min α] {xs : List α} (min_eq_or : ∀ a b : α, a ∈ xs → b ∈ xs → min a b = a ∨ min a b = b) {a : α} :
    xs.min? = some a → a ∈ xs := by
  match xs with
  | List.nil => simp
  | x :: xs =>
    simp only [List.min?_cons', Option.some.injEq, List.mem_cons]
    intro eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons y xs ind =>
      simp at eq
      have hxy : min x y = x ∨ min x y = y := min_eq_or x y (List.mem_cons_self _ _) (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
      have p := ind _ ?_ eq
      · cases p with
        | inl p =>
          cases hxy with | _ q => simp [p, q]
        | inr p => simp [p, List.mem_cons]
      · intro a b ha hb
        apply min_eq_or
        · refine hxy.elim (fun hxy => (List.mem_cons.1 ha).elim ?_ ?_) (fun hxy => (List.mem_cons.1 ha).elim ?_ ?_)
          · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_self _ _
          · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
          · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)
          · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
        · refine hxy.elim (fun hxy => (List.mem_cons.1 hb).elim ?_ ?_) (fun hxy => (List.mem_cons.1 hb).elim ?_ ?_)
          · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_self _ _
          · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
          · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)
          · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem List.min?_eq_head? {α : Type u} [Min α] {l : List α} (h : l.Pairwise (fun a b => min a b = a)) : l.min? = l.head? := by
  cases l with
  | nil => simp
  | cons x l =>
    rw [List.head?_cons, List.min?_cons', Option.some.injEq]
    induction l generalizing x with
    | nil => simp
    | cons y l ih =>
      have hx : min x y = x := List.rel_of_pairwise_cons h (List.mem_cons_self _ _)
      rw [List.foldl_cons, ih _ (hx.symm ▸ h.sublist (by simp)), hx]

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

theorem Ordering.isLE_of_eq_eq {o : Ordering} : o = .eq → o.isLE := by
  rintro rfl; rfl

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

namespace Std.DHashMap.Internal.List

@[simp]
theorem getEntry_fst [BEq α] {xs : List ((a : α) × β a)} {k : α} (h : containsKey k xs) :
    (getEntry k xs h).1 = getKey k xs h := by
  induction xs using assoc_induction
  · simp at h
  · next k' v' l ih =>
    cases hkk' : k' == k
    · rw [getEntry_cons_of_false hkk', getKey_cons]
      simp [hkk', ih]
    · rw [getEntry_cons_of_beq hkk', getKey_cons]
      simp [hkk']

theorem getKey_beq [BEq α] {xs : List ((a : α) × β a)} {k : α} (h : containsKey k xs) :
    getKey k xs h == k := by
  induction xs using assoc_induction
  · simp at h
  · next k' v' l ih =>
    rw [getKey_cons]
    split
    · assumption
    · apply ih

end Std.DHashMap.Internal.List

variable [Ord α]

-- TODO: mark Ordering.isLE as @[inline]

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

theorem compare_eq_gt_iff [OrientedOrd α] {a b : α} : compare a b = .gt ↔ compare b a = .lt := by
  rw [OrientedOrd.eq_swap]
  cases compare b a <;> simp

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

theorem not_lt_of_lt [OrientedOrd α] {a b : α} (h : a < b) : ¬b < a :=
  not_lt_iff_le.2 (le_of_lt h)

theorem lt_iff' [OrientedOrd α] {a b : α} : a < b ↔ compare b a = .gt := by
  rw [lt_iff, compare_eq_gt_iff]

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

local instance equivBEqOfTransOrd [TransOrd α] : EquivBEq α where
  symm := beq_symm
  trans := beq_trans
  refl := beq_refl

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


-- local instance : Min α where
--   min a b := if a ≤ b then a else b

-- theorem min_def {a b : α} : min a b = if a ≤ b then a else b := rfl

-- -- Is this provable without `TransOrd`?
-- local instance [TransOrd α] : Std.Associative (min : α → α → α) where
--   assoc a b c := by
--     simp only [min_def]
--     split <;> split <;> (try split) <;> try rfl
--     · rename_i hab hac hbc
--       have := le_trans hab hbc
--       contradiction
--     · rename_i hab hbc hac
--       rw [not_le_iff_lt] at hab hbc
--       have := lt_trans hbc hab
--       rw [← not_lt_iff_le] at hac
--       contradiction

local instance : Min ((a : α) × β a) where
  min a b := if a.1 ≤ b.1 then a else b

theorem min_def' {p q : (a : α) × β a} : min p q = if p.1 ≤ q.1 then p else q := rfl

theorem min_eq_or {p q : (a : α) × β a} : min p q = p ∨ min p q = q := by
  rw [min_def']
  split <;> simp

theorem min_eq_left' {p q : (a : α) × β a} (h : p.1 ≤ q.1) : min p q = p := by
  simp [min_def', h]

theorem min_eq_left_of_lt' {p q : (a : α) × β a} (h : p.1 < q.1) : min p q = p :=
  min_eq_left' (le_of_lt h)

-- Is this provable without `TransOrd`?
local instance [TransOrd α] : Std.Associative (min : (a : α) × β a → (a : α) × β a → (a : α) × β a) where
  assoc a b c := by
    simp only [min_def']
    split <;> split <;> (try split) <;> try rfl
    · rename_i hab hac hbc
      have := le_trans hab hbc
      contradiction
    · rename_i hab hbc hac
      rw [not_le_iff_lt] at hab hbc
      have := lt_trans hbc hab
      rw [← not_lt_iff_le] at hac
      contradiction

namespace Std.DHashMap.Internal.List

theorem eq_append [TransOrd α] {l : List ((a : α) × β a)} (hl : l.Pairwise (·.1 < ·.1)) {k : α} :
    l = l.filter (·.1 < k) ++ ((l.find? (·.1 == k)).toList ++ l.filter (k < ·.1)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases lt_or_lt_or_beq x.1 k with hx|hx|hx
    · simpa [List.filter_cons, hx, not_lt_of_lt hx, List.find?_cons, beq_eq_false_of_lt hx] using ih hl.of_cons
    · have h₁ (y) (hy : y ∈ l) : ¬(decide (y.1 < k)) = true := by
        simp only [decide_eq_true_eq]
        exact not_lt_of_lt (lt_trans hx (List.rel_of_pairwise_cons hl hy))
      have h₂ (y) (hy : y ∈ l) : ¬(y.1 == k) = true := by
        simp only [Bool.not_eq_true]
        exact BEq.symm_false (beq_eq_false_of_lt (lt_trans hx (List.rel_of_pairwise_cons hl hy)))
      simpa [List.filter_cons, hx, not_lt_of_lt hx, List.find?_cons, BEq.symm_false (beq_eq_false_of_lt hx),
        List.filter_eq_nil_iff.2 h₁, List.find?_eq_none.2 h₂] using ih hl.of_cons
    · have h₁ (y) (hy : y ∈ l) : ¬(decide (y.1 < k)) = true := by
        simp only [decide_eq_true_eq]
        exact not_lt_of_lt (lt_of_beq_of_lt (BEq.symm hx) (List.rel_of_pairwise_cons hl hy))
      have h₂ (y) (hy : y ∈ l) : ¬(y.1 == k) = true := by
        simp only [Bool.not_eq_true]
        refine BEq.symm_false (beq_eq_false_of_lt (lt_of_beq_of_lt (BEq.symm hx) (List.rel_of_pairwise_cons hl hy)))
      simpa [List.filter_cons, List.filter_eq_nil_iff.2 h₁, not_lt_of_beq hx, not_lt_of_beq (BEq.symm hx),
        List.find?_cons, hx, List.find?_eq_none.2 h₂] using ih hl.of_cons

/-- The smallest element of `xs` that is not less than `k`. -/
def lowerBound? (xs : List ((a : α) × β a)) (k : α) : Option ((a : α) × β a) :=
  xs.filter (fun p => k ≤ p.1) |>.min?

theorem lowerBound?_mem {xs : List ((a : α) × β a)} {k : α} {p : (a : α) × β a} (h : lowerBound? xs k = some p) :
    p ∈ xs := by
  rw [lowerBound?] at h
  have := List.min?_mem (@min_eq_or _ _ _) h
  simp at this
  exact this.1

/-- The smallest element of `xs` that is greater than `k`. -/
def upperBound? (xs : List ((a : α) × β a)) (k : α) : Option ((a : α) × β a) :=
  xs.filter (fun p => p.1 < k) |>.min?

@[simp]
theorem lowerBound?_nil {k : α} : lowerBound? ([] : List ((a : α) × β a)) k = none := rfl

theorem lowerBound?_cons [TransOrd α] (l : List ((a : α) × β a)) (k : α) (v : β k) (a : α) :
    lowerBound? (⟨k, v⟩ :: l) a =
      if k < a then lowerBound? l a else some ((lowerBound? l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
  rw [lowerBound?, List.filter_cons]
  simp only [decide_eq_true_eq]
  split
  · rw [List.min?_cons]
    split
    · exact False.elim (not_lt_self (lt_of_le_of_lt (b := k) ‹_› ‹_›))
    · rfl
  · next h =>
    rw [not_le_iff_lt] at h
    simp [h, lowerBound?]

theorem lowerBound?_cons_eq_self [TransOrd α] {l : List ((a : α) × β a)} {p : (a : α) × β a} {k : α}
    (hp : k ≤ p.1) (hl : ∀ q ∈ l, q.1 < k ∨ p.1 ≤ q.1) : lowerBound? (p :: l) k = some p := by
  rw [lowerBound?_cons]
  simp only [not_lt_iff_le.2 hp, ↓reduceIte, Option.some.injEq]
  rw [lowerBound?]
  cases h : (l.filter (fun p => k ≤ p.1)).min? with
  | none => simp
  | some q =>
    have := List.mem_filter.1 (List.min?_mem (fun _ _ => min_eq_or) h)
    simp only [decide_eq_true_eq] at this
    suffices p.1 ≤ q.1 by simpa using min_eq_left' this
    exact (hl _ this.1).resolve_left (not_lt_iff_le.2 this.2)

theorem min_comm_of_lt_or_lt [OrientedOrd α] {p p' : (a : α) × β a} (h : p.1 < p'.1 ∨ p'.1 < p.1) :
    min p p' = min p' p := by
  rcases h with h|h <;> simp [min_def', le_of_lt h, not_le_iff_lt.2 h]

theorem lt_or_lt_of_containsKey_eq_false [TransOrd α] {l : List ((a : α) × β a)} {p : (a : α) × β a} {k : α}
    (hp : p ∈ l) (hk : containsKey k l = false) : p.1 < k ∨ k < p.1 := by
  rcases lt_or_lt_or_beq p.1 k with h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · rw [containsKey_congr (BEq.symm h), containsKey_of_mem hp] at hk
    contradiction

theorem lowerBound?_of_perm [TransOrd α] {l l' : List ((a : α) × β a)} (hll' : List.Perm l l') {k : α} (hl : DistinctKeys l) :
    lowerBound? l k = lowerBound? l' k := by
  induction hll' with
  | nil => rfl
  | @cons x l l' _ ih => rw [lowerBound?_cons, lowerBound?_cons, ih hl.tail]
  | swap x y l =>
    rw [lowerBound?_cons, lowerBound?_cons, lowerBound?_cons, lowerBound?_cons]
    split <;> split <;> try (simp; done)
    rename_i hyk hxk
    have hxy : x.1 < y.1 ∨ y.1 < x.1 :=
      lt_or_lt_of_containsKey_eq_false (List.mem_cons_self _ _) hl.containsKey_eq_false
    cases lowerBound? l k with
    | none => simpa using (min_comm_of_lt_or_lt hxy).symm
    | some p => simp [← Std.Associative.assoc (op := min), min_comm_of_lt_or_lt hxy]
  | trans h₁ _ ih₁ ih₂ => rw [ih₁ hl, ih₂ (hl.perm h₁.symm)]

theorem lowerBound?_replaceEntry_cons_of_beq [TransOrd α] {l : List ((a : α) × β a)}
    {k a : α} {v : β k} {p : (a : α) × β a} (h : p.1 == k) : lowerBound? (replaceEntry k v (p :: l)) a =
      if k < a then lowerBound? l a else some ((lowerBound? l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
  rw [replaceEntry_cons_of_true h, lowerBound?_cons]

theorem lowerBound?_replaceEntry_of_containsKey_eq_true [TransOrd α] {l : List ((a : α) × β a)}
      {k : α} {v : β k} {a : α} (h : containsKey k l) (hl : DistinctKeys l) :
    lowerBound? (replaceEntry k v l) a = if k < a then lowerBound? l a else some ((lowerBound? l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
  obtain ⟨l', hl'⟩ := perm_cons_getEntry h
  rw [lowerBound?_of_perm (replaceEntry_of_perm hl hl') hl.replaceEntry]
  rw [lowerBound?_replaceEntry_cons_of_beq (by simpa using getKey_beq _)]
  rw [lowerBound?_of_perm hl' hl, lowerBound?_cons]
  split <;> split
  · rfl
  · rename_i h₁ h₂
    simp only [getEntry_fst] at h₂
    have h₁' := lt_of_beq_of_lt (getKey_beq h) h₁
    contradiction
  · simp
  · have hk : k ≤ getKey k l h := le_of_beq (BEq.symm (getKey_beq h))
    cases lowerBound? l' a with
    | none => simp [min_def', hk]
    | some p =>
      simp only [Option.elim_some, Option.some.injEq]
      rw [← Std.Associative.assoc (op := min)]
      congr 1
      simp [min_def', hk]

theorem lowerBound?_insertEntry [TransOrd α] (xs : List ((a : α) × β a)) (k : α) (v : β k) (a : α) (h : DistinctKeys xs) :
    lowerBound? (insertEntry k v xs) a =
      if k < a then lowerBound? xs a else some ((lowerBound? xs a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
  rw [insertEntry]
  cases hc : containsKey k xs
  · rw [cond_false, lowerBound?_cons]
  · rw [cond_true, lowerBound?_replaceEntry_of_containsKey_eq_true hc h]

theorem lowerBound?_append_of_forall_mem_left [TransOrd α] {l₁ l₂ : List ((a : α) × β a)} {k : α} (h : ∀ p ∈ l₁, p.1 < k) :
    lowerBound? (l₁ ++ l₂) k = lowerBound? l₂ k := by
  rw [lowerBound?, lowerBound?, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append]
  exact fun p hp => by simpa using not_le_iff_lt.2 (h p hp)

theorem lowerBound?_eq_head? {l : List ((a : α) × β a)} {k : α} (h : ∀ p ∈ l, k ≤ p.1) (hl : l.Pairwise (fun a b => a.1 < b.1)) :
    lowerBound? l k = l.head? := by
  rw [lowerBound?, List.filter_eq_self.2 (decide_eq_true <| h · ·), List.min?_eq_head? (hl.imp min_eq_left_of_lt')]

/-- The number of entries whose key is strictly less than the given key. -/
def rank (k : α) (l : List ((a : α) × β a)) : Nat :=
  l.filter (·.1 < k) |>.length

theorem rank_append_eq_left [OrientedOrd α] {k : α} {l₁ l₂ : List ((a : α) × β a)} (hl₂ : ∀ p ∈ l₂, k ≤ p.1) :
    rank k (l₁ ++ l₂) = rank k l₁ := by
  simpa [rank, not_lt_iff_le]

theorem rank_eq_length {k : α} {l : List ((a : α) × β a)} (hl : ∀ p ∈ l, p.1 < k) :
    rank k l = l.length := by
  simpa [rank]

end Std.DHashMap.Internal.List
