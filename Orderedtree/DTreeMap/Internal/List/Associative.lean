/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Data.DHashMap.Internal.List.Associative
import Orderedtree.Classes.TransOrd

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

-- theorem Option.unattach_eq_some {α : Type u} {p : α → Prop} {a : α} {o : Option { x // p x}} : o.unattach = some a ↔ ∃ h : p a, o = some ⟨a, h⟩ :=
--   o.rec (by simp) (fun h => ⟨by simp only [unattach_some, some.injEq]; rintro rfl; exact ⟨h.2, rfl⟩,
--     by simp only [some.injEq, unattach_some, forall_exists_index]; rintro hx rfl; rfl⟩)

-- unused
-- theorem List.min?_mem₂ {α : Type u} [Min α] {xs : List α} (min_eq_or : ∀ a b : α, a ∈ xs → b ∈ xs → min a b = a ∨ min a b = b) {a : α} :
--     xs.min? = some a → a ∈ xs := by
--   match xs with
--   | List.nil => simp
--   | x :: xs =>
--     simp only [List.min?_cons', Option.some.injEq, List.mem_cons]
--     intro eq
--     induction xs generalizing x with
--     | nil =>
--       simp at eq
--       simp [eq]
--     | cons y xs ind =>
--       simp at eq
--       have hxy : min x y = x ∨ min x y = y := min_eq_or x y (List.mem_cons_self _ _) (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
--       have p := ind _ ?_ eq
--       · cases p with
--         | inl p =>
--           cases hxy with | _ q => simp [p, q]
--         | inr p => simp [p, List.mem_cons]
--       · intro a b ha hb
--         apply min_eq_or
--         · refine hxy.elim (fun hxy => (List.mem_cons.1 ha).elim ?_ ?_) (fun hxy => (List.mem_cons.1 ha).elim ?_ ?_)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_self _ _
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
--         · refine hxy.elim (fun hxy => (List.mem_cons.1 hb).elim ?_ ?_) (fun hxy => (List.mem_cons.1 hb).elim ?_ ?_)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_self _ _
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

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

-- TODO: mark Ordering.isLE as @[inline]

def minSigmaOfOrd [Ord α] : Min ((a : α) × β a) where
  min a b := if compare a.1 b.1 |>.isLE then a else b

attribute [local instance] minSigmaOfOrd

theorem min_def [Ord α] {p q : (a : α) × β a} : min p q = if compare p.1 q.1 |>.isLE then p else q := rfl

theorem min_eq_or [Ord α] {p q : (a : α) × β a} : min p q = p ∨ min p q = q := by
  rw [min_def]
  split <;> simp

theorem min_eq_left [Ord α] {p q : (a : α) × β a} (h : compare p.1 q.1 |>.isLE) : min p q = p := by
  simp [min_def, h]

theorem min_eq_left_of_lt [Ord α] {p q : (a : α) × β a} (h : compare p.1 q.1 = .lt) : min p q = p :=
  min_eq_left (Ordering.isLE_of_eq_lt h)

-- Is this provable without `TransOrd`?
local instance [Ord α] [TransOrd α] : Std.Associative (min : (a : α) × β a → (a : α) × β a → (a : α) × β a) where
  assoc a b c := by
    simp only [min_def]
    split <;> split <;> (try split) <;> try rfl
    · rename_i hab hac hbc
      have := TransCmp.le_trans hab hbc
      contradiction
    · rename_i hab hbc hac
      simp only [Bool.not_eq_true, Ordering.isLE_eq_false] at hab hbc
      refine absurd hac ?_
      simp only [Bool.not_eq_true, Ordering.isLE_eq_false]
      exact OrientedCmp.gt_of_lt (TransCmp.lt_trans (OrientedCmp.lt_of_gt hbc) (OrientedCmp.lt_of_gt hab))

namespace Std.DHashMap.Internal.List

/-- The smallest element of `xs` that is not less than `k`. -/
def lowerBound? [Ord α] (k : α) (xs : List ((a : α) × β a)) : Option ((a : α) × β a) :=
  xs.filter (fun p => compare k p.1 |>.isLE) |>.min?

/-- Like `List.min?`, but using an `Ord` typeclass instead of a `Min` typeclass. -/
def min?' [Ord α] (xs : List ((a : α) × β a)) : Option ((a : α) × β a) :=
  xs.min?

theorem lowerBound?_mem [Ord α] {xs : List ((a : α) × β a)} {k : α} {p : (a : α) × β a} (h : lowerBound? k xs = some p) :
    p ∈ xs := by
  rw [lowerBound?] at h
  have := List.min?_mem (@min_eq_or _ _ _) h
  simp at this
  exact this.1

/-- The smallest element of `xs` that is greater than `k`. -/
def upperBound? [Ord α] (xs : List ((a : α) × β a)) (k : α) : Option ((a : α) × β a) :=
  xs.filter (fun p => compare k p.1 = .lt) |>.min?

@[simp]
theorem lowerBound?_nil [Ord α] {k : α} : lowerBound? k ([] : List ((a : α) × β a)) = none := rfl

-- theorem lowerBound?_cons [Ord α] [TransOrd α] (l : List ((a : α) × β a)) (k : α) (v : β k) (a : α) :
--     lowerBound? (⟨k, v⟩ :: l) a =
--       if compare k a = .lt then lowerBound? l a else some ((lowerBound? l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   rw [lowerBound?, List.filter_cons]
--   simp only [decide_eq_true_eq]
--   split
--   · rw [List.min?_cons]
--     split
--     · exact False.elim (not_lt_self (lt_of_le_of_lt (b := k) ‹_› ‹_›))
--     · rfl
--   · next h =>
--     rw [not_le_iff_lt] at h
--     simp [h, lowerBound?]

-- theorem lowerBound?_cons_eq_self [TransOrd α] {l : List ((a : α) × β a)} {p : (a : α) × β a} {k : α}
--     (hp : k ≤ p.1) (hl : ∀ q ∈ l, q.1 < k ∨ p.1 ≤ q.1) : lowerBound? (p :: l) k = some p := by
--   rw [lowerBound?_cons]
--   simp only [not_lt_iff_le.2 hp, ↓reduceIte, Option.some.injEq]
--   rw [lowerBound?]
--   cases h : (l.filter (fun p => k ≤ p.1)).min? with
--   | none => simp
--   | some q =>
--     have := List.mem_filter.1 (List.min?_mem (fun _ _ => min_eq_or) h)
--     simp only [decide_eq_true_eq] at this
--     suffices p.1 ≤ q.1 by simpa using min_eq_left' this
--     exact (hl _ this.1).resolve_left (not_lt_iff_le.2 this.2)

-- theorem min_comm_of_lt_or_lt [OrientedOrd α] {p p' : (a : α) × β a} (h : p.1 < p'.1 ∨ p'.1 < p.1) :
--     min p p' = min p' p := by
--   rcases h with h|h <;> simp [min_def', le_of_lt h, not_le_iff_lt.2 h]

-- theorem lt_or_lt_of_containsKey_eq_false [TransOrd α] {l : List ((a : α) × β a)} {p : (a : α) × β a} {k : α}
--     (hp : p ∈ l) (hk : containsKey k l = false) : p.1 < k ∨ k < p.1 := by
--   rcases lt_or_lt_or_beq p.1 k with h|h|h
--   · exact Or.inl h
--   · exact Or.inr h
--   · rw [containsKey_congr (BEq.symm h), containsKey_of_mem hp] at hk
--     contradiction

-- theorem lowerBound?_of_perm [TransOrd α] {l l' : List ((a : α) × β a)} (hll' : List.Perm l l') {k : α} (hl : DistinctKeys l) :
--     lowerBound? l k = lowerBound? l' k := by
--   induction hll' with
--   | nil => rfl
--   | @cons x l l' _ ih => rw [lowerBound?_cons, lowerBound?_cons, ih hl.tail]
--   | swap x y l =>
--     rw [lowerBound?_cons, lowerBound?_cons, lowerBound?_cons, lowerBound?_cons]
--     split <;> split <;> try (simp; done)
--     rename_i hyk hxk
--     have hxy : x.1 < y.1 ∨ y.1 < x.1 :=
--       lt_or_lt_of_containsKey_eq_false (List.mem_cons_self _ _) hl.containsKey_eq_false
--     cases lowerBound? l k with
--     | none => simpa using (min_comm_of_lt_or_lt hxy).symm
--     | some p => simp [← Std.Associative.assoc (op := min), min_comm_of_lt_or_lt hxy]
--   | trans h₁ _ ih₁ ih₂ => rw [ih₁ hl, ih₂ (hl.perm h₁.symm)]

-- theorem lowerBound?_replaceEntry_cons_of_beq [TransOrd α] {l : List ((a : α) × β a)}
--     {k a : α} {v : β k} {p : (a : α) × β a} (h : p.1 == k) : lowerBound? (replaceEntry k v (p :: l)) a =
--       if k < a then lowerBound? l a else some ((lowerBound? l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   rw [replaceEntry_cons_of_true h, lowerBound?_cons]

-- theorem lowerBound?_replaceEntry_of_containsKey_eq_true [TransOrd α] {l : List ((a : α) × β a)}
--       {k : α} {v : β k} {a : α} (h : containsKey k l) (hl : DistinctKeys l) :
--     lowerBound? (replaceEntry k v l) a = if k < a then lowerBound? l a else some ((lowerBound? l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   obtain ⟨l', hl'⟩ := perm_cons_getEntry h
--   rw [lowerBound?_of_perm (replaceEntry_of_perm hl hl') hl.replaceEntry]
--   rw [lowerBound?_replaceEntry_cons_of_beq (by simpa using getKey_beq _)]
--   rw [lowerBound?_of_perm hl' hl, lowerBound?_cons]
--   split <;> split
--   · rfl
--   · rename_i h₁ h₂
--     simp only [getEntry_fst] at h₂
--     have h₁' := lt_of_beq_of_lt (getKey_beq h) h₁
--     contradiction
--   · simp
--   · have hk : k ≤ getKey k l h := le_of_beq (BEq.symm (getKey_beq h))
--     cases lowerBound? l' a with
--     | none => simp [min_def', hk]
--     | some p =>
--       simp only [Option.elim_some, Option.some.injEq]
--       rw [← Std.Associative.assoc (op := min)]
--       congr 1
--       simp [min_def', hk]

-- theorem lowerBound?_insertEntry [TransOrd α] (xs : List ((a : α) × β a)) (k : α) (v : β k) (a : α) (h : DistinctKeys xs) :
--     lowerBound? (insertEntry k v xs) a =
--       if k < a then lowerBound? xs a else some ((lowerBound? xs a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   rw [insertEntry]
--   cases hc : containsKey k xs
--   · rw [cond_false, lowerBound?_cons]
--   · rw [cond_true, lowerBound?_replaceEntry_of_containsKey_eq_true hc h]

theorem lowerBound?_append_of_forall_mem_left [Ord α] [TransOrd α] {l₁ l₂ : List ((a : α) × β a)}
    {k : α} (h : ∀ p ∈ l₁, compare k p.1 = .gt) :
    lowerBound? k (l₁ ++ l₂) = lowerBound? k l₂ := by
  rw [lowerBound?, lowerBound?, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append]
  refine fun p hp => by simpa using h p hp

theorem min?'_eq_head? [Ord α] {l : List ((a : α) × β a)}
    (hl : l.Pairwise (fun a b => compare a.1 b.1 = .lt)) : min?' l = l.head? := by
  rw [min?', List.min?_eq_head? (hl.imp min_eq_left_of_lt)]

theorem lowerBound?_eq_head? [Ord α] {l : List ((a : α) × β a)} {k : α} (h : ∀ p ∈ l, compare k p.1 |>.isLE)
    (hl : l.Pairwise (fun a b => compare a.1 b.1 = .lt)) : lowerBound? k l = l.head? := by
  rw [lowerBound?, List.filter_eq_self.2 h, List.min?_eq_head? (hl.imp min_eq_left_of_lt)]

/-
/-- The number of entries whose key is strictly less than the given key. -/
def rank (k : α) (l : List ((a : α) × β a)) : Nat :=
  l.filter (·.1 < k) |>.length

theorem rank_append_eq_left [OrientedOrd α] {k : α} {l₁ l₂ : List ((a : α) × β a)} (hl₂ : ∀ p ∈ l₂, k ≤ p.1) :
    rank k (l₁ ++ l₂) = rank k l₁ := by
  simpa [rank, not_lt_iff_le]

theorem rank_eq_length {k : α} {l : List ((a : α) × β a)} (hl : ∀ p ∈ l, p.1 < k) :
    rank k l = l.length := by
  simpa [rank]-/

end Std.DHashMap.Internal.List
