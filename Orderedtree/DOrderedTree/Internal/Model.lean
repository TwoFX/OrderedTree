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
def updateAtKey [Ord α] (k : α) (f : Option ((a : α) × β a) → Option ((a : α) × β a)) :
    Impl α β → Impl α β
| leaf => match f none with
          | none => .leaf
          | some ⟨k', v'⟩ => .inner 1 k' v' .leaf .leaf
| inner sz ky y l r =>
  match compare k ky with
  | .lt =>
      let newL := updateAtKey k f l
      balanceSlow ky y newL r
  | .eq => match f (some ⟨ky, y⟩) with
           | none => glueSlow l r
           | some ⟨ky', y'⟩ => .inner sz ky' y' l r
  | .gt =>
      let newR := updateAtKey k f r
      balanceSlow ky y l newR

/-- Model implementation of the `contains` function. -/
def containsₘ [Ord α] (k : α) (l : Impl α β) : Bool :=
  queryAtKey k Option.isSome l

/-- Model implementation of the `insert` function. -/
def insertₘ [Ord α] (k : α) (v : β k) (l : Impl α β) : Impl α β :=
  updateAtKey k (fun _ => some ⟨k, v⟩) l

theorem contains_eq_containsₘ [Ord α] (k : α) (l : Impl α β) :
    l.contains k = l.containsₘ k := by
  induction l using Impl.contains.induct k <;> simp_all [contains, containsₘ, queryAtKey]

theorem balanceR_eq_balance' {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr hlr'} :
    balanceR k v l r hlb hrb hlr = balance k v l r hlb hrb hlr' := by
  rw [balanceR.eq_def, balance.eq_def]
  split
  · dsimp only
    split
    all_goals dsimp only
    contradiction
  · dsimp only
    split
    · dsimp only
      split
      all_goals try (exfalso; tree_tac)
      congr
      tree_tac
    · dsimp only
      split
      · split
        · dsimp only
        · contradiction
        · contradiction
      · split
        · split
          · split
            · exfalso; tree_tac
            · exfalso; tree_tac
          · contradiction
          · contradiction
        · rfl

theorem balanceR_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balance k v l r hlb hrb (by tree_tac) :=
  balanceR_eq_balance'

-- This needs to be improved to balanceL_eq_balanceLErase and balanceLErase_eq_balance

theorem balanceL_eq_balance' {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr hlr'} :
    balanceL k v l r hlb hrb hlr = balance k v l r hlb hrb hlr' := by
  rw [balanceL.eq_def, balance.eq_def]
  split
  · dsimp only
    split
    all_goals dsimp only
    contradiction
  · dsimp only
    split
    · dsimp only
      split
      all_goals try (exfalso; tree_tac)
      congr
      tree_tac
    · dsimp only
      split
      · split
        · split
          · rename_i h
            split
            · exfalso; tree_tac
            · simp [h]
          · rename_i h
            split
            · exfalso; tree_tac
            · simp [h]
        · contradiction
        · contradiction
      · split
        · exfalso; tree_tac
        · rfl

theorem balanceL_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balance k v l r hlb hrb (by tree_tac) :=
  balanceL_eq_balance'

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

theorem balance_eq_balanceSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
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
    (insert k v l h).impl = insertₘ k v l := by
  induction l, h using insert.induct k v <;>
    simp_all [insert, insertₘ, updateAtKey, balanceL_eq_balance, balanceR_eq_balance,
      balance_eq_balanceSlow]

end Impl

end Std.DOrderedTree.Internal
