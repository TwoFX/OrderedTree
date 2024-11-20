/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Model
import Orderedtree.Classes.TransOrd

/-!
# Low-level proofs about size-bounded trees
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type v}

namespace Std.DOrderedTree.Internal.Impl

@[simp] theorem toListModel_leaf : (.leaf : Impl α β).toListModel = [] := rfl
@[simp] theorem toListModel_inner {sz k v l r} :
  (.inner sz k v l r : Impl α β).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := rfl

/-!
## `toListModel` for balancing operations
-/

@[simp]
theorem toListModel_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balance k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balance.eq_def]
  repeat' (split; try dsimp only)
  all_goals
    try contradiction
    try simp; done
  all_goals
    rename_i l r _ _ _
    cases l <;> cases r <;> (try simp; done) <;> (exfalso; tree_tac)

@[simp]
theorem toListModel_balanceL {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceL k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceL_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_balanceLErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceLErase k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceLErase_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_balanceR {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceR k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceR_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_balanceRErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceRErase k v l r hlb hrb hlr).toListModel = l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  rw [balanceRErase_eq_balance, toListModel_balance]

@[simp]
theorem toListModel_minView {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    ⟨(minView k v l r hl hr hlr).k, (minView k v l r hl hr hlr).v⟩ ::
      (minView k v l r hl hr hlr).tree.impl.toListModel =
    l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  induction k, v, l, r, hl, hr, hlr using minView.induct
  · simp [minView]
  · rename_i ih
    simp [minView, ← ih]

@[simp]
theorem toListModel_maxView {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).tree.impl.toListModel ++
      [⟨(maxView k v l r hl hr hlr).k, (maxView k v l r hl hr hlr).v⟩] =
    l.toListModel ++ ⟨k, v⟩ :: r.toListModel := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;> simp_all [maxView]

@[simp]
theorem toListModel_glue {l r : Impl α β} {hl hr hlr} :
    (glue l r hl hr hlr).toListModel = l.toListModel ++ r.toListModel := by
  cases l <;> cases r
  all_goals try (simp [glue]; done)
  dsimp only [glue]
  split <;> try (simp; done)
  rw [toListModel_balanceRErase, ← List.singleton_append, ← List.append_assoc]
  simp

/-!
## Verification of model functions
-/

theorem Ordered.left [Ord α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered) :
    l.Ordered :=
  h.sublist (by simp)

theorem Ordered.right [Ord α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered) :
    r.Ordered :=
  h.sublist (by simp)

theorem Ordered.compare_left [Ord α] {sz k v l r} (h : (.inner sz k v l r : Impl α β).Ordered)
    {k'} (hk' : k' ∈ l.toListModel) : compare k'.1 k = .lt :=
  h.rel_of_mem_append hk' (List.mem_cons_self _ _)

theorem Ordered.compare_left_beq_gt [Ord α] [TransOrd α] {k : α} {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (compare k' k).isLE)
    (p) (hp : p ∈ l.toListModel) : compare k p.1 == .gt :=
 beq_iff_eq.2 (OrientedCmp.gt_of_lt (TransCmp.lt_of_lt_of_isLE (ho.compare_left hp) hcmp))

theorem Ordered.compare_left_not_beq_eq [Ord α] [TransOrd α] {k : α} {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (compare k' k).isLE)
    (p) (hp : p ∈ l.toListModel) : ¬(compare k p.1 == .eq) := by
  suffices compare p.fst k = .lt by simp [this, OrientedCmp.eq_comm (a := k)]
  exact TransCmp.lt_of_lt_of_isLE (ho.compare_left hp) hcmp

theorem Ordered.compare_right [Ord α] {sz k v l r}
    (h : (.inner sz k v l r : Impl α β).Ordered) {k'} (hk' : k' ∈ r.toListModel) :
    compare k k'.1 = .lt := by
  exact List.rel_of_pairwise_cons (h.sublist (List.sublist_append_right _ _)) hk'

theorem Ordered.compare_right_not_beq_gt [Ord α] [TransOrd α] {k : α} {sz k' v' l r}
    (ho : (.inner sz k' v' l r : Impl α β).Ordered) (hcmp : (compare k k').isLE)
    (p) (hp : p ∈ r.toListModel) : ¬(compare k p.1 == .gt) := by
  suffices compare k p.fst = .lt by simp [this]
  exact TransCmp.lt_of_isLE_of_lt hcmp (ho.compare_right hp)

theorem toListModel_filter_gt_of_gt [Ord α] [TransOrd α] {k : α} {sz k' v' l r}
    (hcmp : compare k k' = .gt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (compare k ·.1 == .gt) =
      l.toListModel ++ ⟨k', v'⟩ :: r.toListModel.filter (compare k ·.1 == .gt) := by
  rw [toListModel_inner, List.filter_append, List.filter_cons_of_pos, List.filter_eq_self.2]
  · exact Ordered.compare_left_beq_gt ho (Ordering.isLE_of_eq_lt (OrientedCmp.lt_of_gt hcmp))
  · simpa

theorem toListModel_filter_gt_of_eq [Ord α] [TransOrd α] {k : α} {sz k' v' l r}
    (hcmp : compare k k' = .eq) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (compare k ·.1 == .gt) = l.toListModel := by
  rw [toListModel_inner, List.filter_append, List.filter_cons_of_neg, List.filter_eq_self.2,
    List.filter_eq_nil_iff.2, List.append_nil]
  · exact Ordered.compare_right_not_beq_gt ho (Ordering.isLE_of_eq_eq hcmp)
  · exact Ordered.compare_left_beq_gt ho (Ordering.isLE_of_eq_eq (OrientedCmp.eq_symm hcmp))
  · simp_all

theorem toListModel_filter_gt_of_lt [Ord α] [TransOrd α] {k : α} {sz k' v' l r}
    (hcmp : compare k k' = .lt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (compare k ·.1 == .gt) =
      l.toListModel.filter (compare k ·.1 == .gt) := by
  rw [toListModel_inner, List.filter_append, (List.filter_eq_nil_iff (l := _ :: _)).2,
    List.append_nil]
  simpa [hcmp] using Ordered.compare_right_not_beq_gt ho (Ordering.isLE_of_eq_lt hcmp)

theorem toListModel_find?_of_gt [Ord α] [TransOrd α] {k : α} {sz k' v' l r}
    (hcmp : compare k k' = .gt) (ho : (inner sz k' v' l r).Ordered) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (compare k ·.1 == .eq) =
      r.toListModel.find? (compare k ·.1 == .eq) := by
  rw [toListModel_inner, List.find?_append, List.find?_eq_none.2, Option.none_or,
    List.find?_cons_of_neg]
  · simp [hcmp]
  · exact Ordered.compare_left_not_beq_eq ho (Ordering.isLE_of_eq_lt (OrientedCmp.lt_of_gt hcmp))

theorem toListModel_find?_of_eq [Ord α] {k : α} {sz k' v' l r} (hcmp : compare k k' = .eq) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (compare k ·.1 == .eq) = some ⟨k', v'⟩ := sorry

theorem toListModel_find?_of_lt [Ord α] {k : α} {sz k' v' l r} (hcmp : compare k k' = .lt) :
    (inner sz k' v' l r : Impl α β).toListModel.find? (compare k ·.1 == .eq) =
      l.toListModel.find? (compare k ·.1 == .eq) := sorry

theorem toListModel_filter_lt_of_gt [Ord α] {k : α} {sz k' v' l r} (hcmp : compare k k' = .gt) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (compare k ·.1 == .lt) =
      r.toListModel.filter (compare k ·.1 == .lt) := sorry

theorem toListModel_filter_lt_of_eq [Ord α] {k : α} {sz k' v' l r} (hcmp : compare k k' = .eq) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (compare k ·.1 == .lt) = r.toListModel := sorry

theorem toListModel_filter_lt_of_lt [Ord α] {k : α} {sz k' v' l r} (hcmp : compare k k' = .lt) :
    (inner sz k' v' l r : Impl α β).toListModel.filter (compare k ·.1 == .lt) =
      l.toListModel.filter (compare k ·.1 == .lt) ++ ⟨k', v'⟩ :: r.toListModel := sorry

theorem toListModel_updateAtKey [Ord α] [TransOrd α] {k : α}
    {f : Option ((a : α) × β a) → Option ((a : α) × β a)} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) :
    (l.updateAtKey k f hlb).impl.toListModel = l.toListModel.filter (compare k ·.1 == .gt) ++
      (f (l.toListModel.find? (compare k ·.1 == .eq))).toList ++
      l.toListModel.filter (compare k ·.1 == .lt) := by
  induction l, hlb using updateAtKey.induct k f
  · simp_all [updateAtKey]
  · simp_all [updateAtKey]
  · rename_i sz k' v' l r hb hcmp l' hl'₁ hl'₂ hup hb' ih
    simp only [updateAtKey, hcmp]
    rw [toListModel_balance, toListModel_filter_gt_of_lt hcmp hlo,
      toListModel_filter_lt_of_lt hcmp, toListModel_find?_of_lt hcmp, ih hlo.left]
    simp
  · rename_i sz k' v' l r hl hcmp hf hl'
    simp only [updateAtKey, hcmp, hf]
    rw [toListModel_glue, toListModel_filter_gt_of_eq hcmp hlo, toListModel_find?_of_eq hcmp, hf,
      toListModel_filter_lt_of_eq hcmp]
    simp
  · rename_i sz k' v' l r hl hcmp k'' v'' hf hl'
    simp only [updateAtKey, hcmp, hf]
    rw [toListModel_inner, toListModel_filter_gt_of_eq hcmp hlo, toListModel_find?_of_eq hcmp,
      toListModel_filter_lt_of_eq hcmp, hf]
    simp
  · rename_i sz k' v' l r hb hcmp l' hl'1 hl'2 hup hb' ih
    simp only [updateAtKey, hcmp]
    rw [toListModel_filter_gt_of_gt hcmp hlo, toListModel_find?_of_gt hcmp hlo,
      toListModel_filter_lt_of_gt hcmp, toListModel_balance, ih hlo.right]
    simp

theorem toListModel_eq_append [Ord α] [TransOrd α] (k : α) {l : Impl α β} (ho : l.Ordered) :
    l.toListModel = l.toListModel.filter (compare k ·.1 == .gt) ++
      (l.toListModel.find? (compare k ·.1 == .eq)).toList ++
      l.toListModel.filter (compare k ·.1 == .lt) := by
  induction l
  · rename_i sz k' v l r ih₁ ih₂
    cases hcmp : compare k k'
    · rw [toListModel_filter_gt_of_lt hcmp ho, toListModel_find?_of_lt hcmp,
        toListModel_filter_lt_of_lt hcmp, toListModel_inner]
      conv => lhs; rw [ih₁ ho.left]
      simp
    · rw [toListModel_filter_gt_of_eq hcmp ho, toListModel_find?_of_eq hcmp,
        toListModel_filter_lt_of_eq hcmp, toListModel_inner]
      simp
    · rw [toListModel_filter_gt_of_gt hcmp ho, toListModel_find?_of_gt hcmp ho,
        toListModel_filter_lt_of_gt hcmp, toListModel_inner]
      conv => lhs; rw [ih₂ ho.right]
      simp
  · simp

theorem Option.pairwise_toList {P : α → α → Prop} {o : Option α} : o.toList.Pairwise P := by
  cases o <;> simp

theorem ordered_updateAtKey [Ord α] [TransOrd α] {k : α}
    {f : Option ((a : α) × β a) → Option ((a : α) × β a)}
    (hf : ∀ p : Option ((a : α) × β a), (∀ p', p = some p' → compare k p'.1 = .eq) →
      ∀ q : (a : α) × β a, f p = q → compare k q.1 = .eq)
    {l : Impl α β} (hlb : l.Balanced) (hlo : l.Ordered) : (l.updateAtKey k f hlb).impl.Ordered := by
  rw [Ordered, toListModel_updateAtKey _ hlo]
  rw [Ordered, toListModel_eq_append k hlo] at hlo
  simp only [List.pairwise_append] at hlo ⊢
  refine ⟨⟨hlo.1.1, Option.pairwise_toList, ?_⟩, ⟨hlo.2.1, ?_⟩⟩
  · intro a ha b hb
    have := hlo.2.2 a (List.mem_append_of_mem_left _ ha)
    clear hlo
    simp at ha hb
    have : compare k b.fst = .eq := by
      refine hf _ (fun p hp => ?_) _ hb
      exact beq_iff_eq.1 (List.find?_eq_some_iff_append.1 hp |>.1)
    exact TransCmp.lt_of_lt_of_eq (OrientedCmp.lt_of_gt ha.2) this
  · intro a ha b hb
    rw [List.mem_append] at ha
    obtain ha|ha := ha
    · exact hlo.2.2 a (List.mem_append_of_mem_left _ ha) _ hb
    · simp at ha
      have h₀ : compare k a.fst = .eq := by
        apply hf _ _ _ ha
        intro p hp
        exact beq_iff_eq.1 (List.find?_eq_some_iff_append.1 hp |>.1)
      have h₁ : compare k b.fst = .lt := by
        simp only [List.mem_filter, beq_iff_eq] at hb
        exact hb.2
      exact TransCmp.lt_of_eq_of_lt (OrientedCmp.eq_symm h₀) h₁

/-!
## Verification of modification operations
-/

/-!
### `empty`
-/

@[simp]
theorem toListModel_empty : (.empty : Impl α β).toListModel = [] := by
  simp [empty]

theorem ordered_empty [Ord α] : (.empty : Impl α β).Ordered := by
  simp [Ordered]

/-!
### `insertₘ`
-/

theorem ordered_insertₘ [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) : (l.insertₘ k v hlb).Ordered := by
  apply ordered_updateAtKey _ _ hlo
  simp

/-!
### `insert`
-/

theorem ordered_insert [Ord α] [TransOrd α] {k : α} {v : β k} {l : Impl α β} (hlb : l.Balanced)
    (hlo : l.Ordered) : (l.insert k v hlb).impl.Ordered := by
  simpa only [insert_eq_insertₘ] using ordered_insertₘ hlb hlo

theorem WF.ordered [Ord α] [TransOrd α] {l : Impl α β} (h : WF l) : l.Ordered := by
  induction h
  · assumption
  · exact ordered_empty
  · exact ordered_insert ‹_› ‹_›

end Std.DOrderedTree.Internal.Impl
