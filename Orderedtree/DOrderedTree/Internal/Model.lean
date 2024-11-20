/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Impl

/-!
# Model implementations of ordered tree functions
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w}

namespace Std.DOrderedTree.Internal

namespace Impl

/-!
## General infrastructure
-/

/-- General "query the value at a given key" function. -/
def queryAtKey [Ord α] (k : α) (f : Option ((a : α) × β a) → δ) (l : Impl α β) : δ :=
  match l with
  | .leaf => f none
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => queryAtKey k f l
    | .eq => f (some ⟨k', v'⟩)
    | .gt => queryAtKey k f r

/-- General "update the mapping for a given key" function. -/
def updateAtKey [Ord α] (k : α) (f : Option ((a : α) × β a) → Option ((a : α) × β a))
    (l : Impl α β) (hl : Balanced l) : Tree₃ α β (l.size - 1) l.size (l.size + 1) :=
  match l with
  | leaf => match f none with
            | none => ⟨.leaf, by tree_tac, by tree_tac⟩
            | some ⟨k', v'⟩ => ⟨.inner 1 k' v' .leaf .leaf, by tree_tac, by tree_tac⟩
  | inner sz ky y l r =>
    match compare k ky with
    | .lt =>
        let ⟨newL, h₁, h₂⟩ := updateAtKey k f l (by tree_tac)
        ⟨balance ky y newL r (by tree_tac) (by tree_tac) (by tree_tac), by tree_tac, by tree_tac⟩
    | .eq => match f (some ⟨ky, y⟩) with
             | none =>
               ⟨glue l r (by tree_tac) (by tree_tac) (by tree_tac), by tree_tac, by tree_tac⟩
             | some ⟨ky', y'⟩ => ⟨.inner sz ky' y' l r, by tree_tac, by tree_tac⟩
    | .gt =>
        let ⟨newR, h₁, h₂⟩ := updateAtKey k f r (by tree_tac)
        ⟨balance ky y l newR (by tree_tac) (by tree_tac) (by tree_tac), by tree_tac, by tree_tac⟩

/-!
## Model functions
-/

/-- Model implementation of the `contains` function. -/
def containsₘ [Ord α] (k : α) (l : Impl α β) : Bool :=
  queryAtKey k Option.isSome l

/-- Model implementation of the `insert` function. -/
def insertₘ [Ord α] (k : α) (v : β k) (l : Impl α β) (h : l.Balanced) : Impl α β :=
  updateAtKey k (fun _ => some ⟨k, v⟩) l h |>.impl

/-!
## Helper theorems for reasoning with key-value pairs
-/

theorem balanceLSlow_pair_congr {k : α} {v : β k} {k' : α} {v' : β k'}
    (h : (⟨k, v⟩ : (a : α) × β a) = ⟨k', v'⟩) {l l' r r' : Impl α β}
    (hl : l = l') (hr : r = r') :
    balanceLSlow k v l r = balanceLSlow k' v' l' r' := by
  cases h; cases hl; cases hr; rfl

theorem balanceRSlow_pair_congr {k : α} {v : β k} {k' : α} {v' : β k'}
    (h : (⟨k, v⟩ : (a : α) × β a) = ⟨k', v'⟩) {l l' r r' : Impl α β}
    (hl : l = l') (hr : r = r') :
    balanceRSlow k v l r = balanceRSlow k' v' l' r' := by
  cases h; cases hl; cases hr; rfl

/-!
## Equivalence of function to model functions
-/

theorem contains_eq_containsₘ [Ord α] (k : α) (l : Impl α β) :
    l.contains k = l.containsₘ k := by
  induction l using Impl.contains.induct k <;> simp_all [contains, containsₘ, queryAtKey]

theorem balanceL_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balance k v l r hlb hrb (by tree_tac) := by
  rw [balanceL_eq_balanceLErase, balanceLErase_eq_balance]

theorem balanceR_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balance k v l r hlb hrb (by tree_tac) := by
  rw [balanceR_eq_balanceRErase, balanceRErase_eq_balance]

theorem balanceL_eq_balanceLSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balanceLSlow k v l r := by
  rw [balanceL.eq_def, balanceLSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balanceLErase_eq_balanceLSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceLErase k v l r hlb hrb hlr = balanceLSlow k v l r := by
  rw [balanceLErase.eq_def, balanceLSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balanceR_eq_balanceRSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balanceRSlow k v l r := by
  rw [balanceR.eq_def, balanceRSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balanceRErase_eq_balanceRSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceRErase k v l r hlb hrb hlr = balanceRSlow k v l r := by
  rw [balanceRErase.eq_def, balanceRSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balance_eq_balanceSlow (k : α) (v : β k) (l r : Impl α β) (hlb hrb hlr) :
    balance k v l r hlb hrb hlr = balanceSlow k v l r := by
  rw [balance.eq_def, balanceSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem minView_k_eq_minViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (minView k v l r hl hr hlr).k = (minViewSlow k v l r).k := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;> simp_all [minView, minViewSlow]

theorem minView_kv_eq_minViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (⟨(minView k v l r hl hr hlr).k, (minView k v l r hl hr hlr).v⟩ : (a : α) × β a) =
      ⟨(minViewSlow k v l r).k, (minViewSlow k v l r).v⟩ := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;>
    simp_all [minView, minViewSlow]

theorem minView_tree_impl_eq_minViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (minView k v l r hl hr hlr).tree.impl = (minViewSlow k v l r).tree := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;>
    simp_all [minView, minViewSlow, balanceRErase_eq_balanceRSlow]

theorem maxView_k_eq_maxViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).k = (maxViewSlow k v l r).k := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;> simp_all [maxView, maxViewSlow]

theorem maxView_kv_eq_maxViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (⟨(maxView k v l r hl hr hlr).k, (maxView k v l r hl hr hlr).v⟩ : (a : α) × β a) =
      ⟨(maxViewSlow k v l r).k, (maxViewSlow k v l r).v⟩ := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;>
    simp_all [maxView, maxViewSlow]

theorem maxView_tree_impl_eq_maxViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).tree.impl = (maxViewSlow k v l r).tree := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;>
    simp_all [maxView, maxViewSlow, balanceLErase_eq_balanceLSlow]

theorem glue_eq_glueSlow {l r : Impl α β} {hl hr hlr} :
    glue l r hl hr hlr = glueSlow l r := by
  rw [glue.eq_def, glueSlow.eq_def]
  split; simp
  split; simp
  dsimp only
  split
  · simpa [*, balanceLErase_eq_balanceLSlow] using balanceLSlow_pair_congr
      minView_kv_eq_minViewSlow rfl minView_tree_impl_eq_minViewSlow
  · simpa [*, balanceRErase_eq_balanceRSlow] using balanceRSlow_pair_congr
      maxView_kv_eq_maxViewSlow maxView_tree_impl_eq_maxViewSlow rfl

theorem insert_eq_insertSlow [Ord α] {k : α} {v : β k} {l : Impl α β} {h} :
    (insert k v l h).impl = insertSlow k v l := by
  induction l, h using insert.induct k v <;>
    simp_all [insert, insertSlow, balanceL_eq_balanceLSlow, balanceR_eq_balanceRSlow]

theorem insert_eq_insertₘ [Ord α] {k : α} {v : β k} {l : Impl α β} {h} :
    (insert k v l h).impl = insertₘ k v l h := by
  induction l, h using insert.induct k v <;>
    simp_all [insert, insertₘ, updateAtKey, balanceL_eq_balance, balanceR_eq_balance,
      balance_eq_balanceSlow]

end Impl

end Std.DOrderedTree.Internal
