/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
universe u v

-- This closely follows the Haskell implementation at https://hackage.haskell.org/package/containers-0.7/docs/src/Data.Map.Internal.html

variable {α : Type u} {β : α → Type v}

namespace Std

inductive DOrderedTree.Raw (α : Type u) (β : α → Type v) where
  | inner (size : Nat) (k : α) (v : β k) (l r : DOrderedTree.Raw α β)
  | leaf

namespace DOrderedTree

namespace Raw

@[inline]
def delta : Nat := 3
@[inline]
def ratio : Nat := 2

@[inline]
def size : Raw α β → Nat
  | inner s _ _ _ _ => s
  | leaf => 0

@[simp] theorem size_leaf : (leaf : Raw α β).size = 0 := rfl

def BalancedAtRoot (left right : Nat) : Prop :=
  left + right ≤ 1 ∨ (left ≤ delta * right ∧ right ≤ delta * left)

theorem balancedAtRoot_leaf_leaf : BalancedAtRoot (leaf : Raw α β).size (leaf : Raw α β).size :=
  Or.inl (by simp)

-- We actually want the Nat subtraction here!
def AlmostBalancedAtRootL (left right : Nat) : Prop :=
  (left - 1) + right ≤ 1 ∨ (left - 1 ≤ delta * right ∧ right ≤ delta * (left - 1))

inductive Balanced : Raw α β → Prop
| leaf : Balanced leaf
| inner {size k v l r} : Balanced l → Balanced r → BalancedAtRoot l.size r.size → size = 1 + l.size + r.size → Balanced (inner size k v l r)

theorem Balanced.root {size k v} {l r : Raw α β} : (Raw.inner size k v l r).Balanced → BalancedAtRoot l.size r.size
| inner _ _ h _ => h

theorem Balanced.pos {size k v} {l r : Raw α β} : (Raw.inner size k v l r).Balanced → 0 < size
| inner _ _ _ h => by omega

theorem Balanced.eq {size k v} {l r : Raw α β} : (Raw.inner size k v l r).Balanced → size = 1 + l.size + r.size
| inner _ _ _ h => h

theorem Balanced.left {size k v} {l r : Raw α β} : (Raw.inner size k v l r).Balanced → l.Balanced
| inner h _ _ _ => h

theorem Balanced.right {size k v} {l r : Raw α β} : (Raw.inner size k v  l r).Balanced → r.Balanced
| inner _ h _ _ => h

theorem Balanced.size_leaf_left {size k v} {r : Raw α β} : (Raw.inner size k v Raw.leaf r).Balanced → size ≤ 2
| inner _ _ h hs => by
    rcases h with (h|⟨-, h⟩)
    all_goals
    · rw [size_leaf] at h
      rw [hs, size_leaf]
      omega

theorem Balanced.size_leaf_right {size k v} {l : Raw α β} : (Raw.inner size k v l Raw.leaf).Balanced → size ≤ 2
| inner _ _ h hs => by
    rcases h with (h|⟨h, -⟩)
    all_goals
    · rw [size_leaf] at h
      rw [hs, size_leaf]
      omega

theorem Balanced.size_eq_zero : {r : Raw α β} → r.Balanced → r.size = 0 → r = .leaf
| Raw.leaf, _, _ => rfl
| Raw.inner _ _ _ _ _, .inner _ _ _ h₁, h₂ => by simp [size] at h₂; omega

theorem balanced_singleton {k : α} {v : β k} : (Raw.inner 1 k v .leaf .leaf).Balanced :=
  .inner .leaf .leaf balancedAtRoot_leaf_leaf (by simp)

instance : Inhabited (Raw α β) where
  default := .leaf

@[inline] def balanceL (k : α) (v : β k) (l r : Raw α β) (hrb : Balanced r) (hlb : Balanced l) (hlr : AlmostBalancedAtRootL l.size r.size) : Raw α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
    | inner ls lk lv (.inner lls _ _ _ _) (.inner lrs _ _ _ _) =>
        False.elim (by
          obtain (h|⟨h, -⟩) := hlr
          all_goals
          · simp only [hlb.eq, size] at h
            have := hlb.left.pos
            have := hlb.right.pos
            omega)
  | (inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | inner ls lk lv ll lr =>
        if hlsd : ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl) (.inner (1 + rs + lrr.size) k v lrr r)
          | leaf, _ => False.elim (by
              rw [delta] at hlsd
              have : 3 < ls := by have := hrb.pos; omega
              have := hlb.size_leaf_left
              omega)
          | _, leaf => False.elim (by
              rw [delta] at hlsd
              have : 3 < ls := by have := hrb.pos; omega
              have := hlb.size_leaf_right
              omega)
        else .inner (1 + ls + rs) k v l r

theorem False.elim' {h : False} {P : α → Prop} : P h.elim :=
  h.elim

theorem balanced_balanceL {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr : AlmostBalancedAtRootL l.size r.size} :
    (balanceL k v l r hrb hlb hlr).Balanced := by
  rw [balanceL.eq_def]
  split
  · split
    · exact balanced_singleton
    · rename_i hlb _ _
      simp [hlb.eq]
      exact .inner balanced_singleton .leaf (Or.inl (by simp [size])) (by simp [size])
    · exact .inner balanced_singleton balanced_singleton (Or.inr ⟨by simp [delta, size], by simp [delta, size]⟩) (by simp [size])
    · rename_i l r hlb _ _
      have := hlb.size_leaf_right
      rw [hlb.eq, hlb.left.eq, size, size_leaf] at this
      -- dsimp only at this
      obtain rfl : l = .leaf := hlb.left.left.size_eq_zero (by omega)
      obtain rfl : r = .leaf := hlb.left.right.size_eq_zero (by omega)
      rw [hlb.left.eq]
      exact .inner (by simpa using balanced_singleton) balanced_singleton (Or.inr ⟨by simp [delta, size], by simp [delta, size]⟩) (by simp [size])
    · exact False.elim'
  · split
    · rename_i hlr _
      refine .inner .leaf ‹_› ?_ (by simp [size])
      rcases hlr with (hlr|⟨-, hlr⟩)
      · simp only [size, Nat.zero_sub, Nat.zero_add] at hlr
        exact Or.inl (by simp only [size]; omega)
      · rename_i hrb _ _ _ _ _
        simp [delta, hrb.eq, size] at hlr
        -- omega
    · split
      · split
        · split
          · rename_i rs _ _ _ _ hrb _ _ _ ls _ _ hdel _ _ _ _ lls _ _ _ _ lrs _ _ _ _ hlb hlr _ hrat
            have : lls + lrs ≤ delta * rs := by
              obtain (hlr|⟨hlr, -⟩) := hlr
              · have := hrb.pos
                simp [size, hlb.eq] at hlr
                omega
              · simp [size, hlb.eq] at hlr
                omega
            have : delta * rs < lls + lrs + 1 := by
              simp [hlb.eq, size] at hdel
              omega
            -- have hlsrs : lls + lrs = delta * rs := by omega
            have : lls ≤ delta * lrs := by
              obtain (hbal|⟨hbal, -⟩) := hlb.root
              · rw [hlb.left.eq, hlb.right.eq] at hbal
                simp [size] at hbal
                omega
              · simpa [size] using hbal
            refine .inner hlb.left (.inner hlb.right hrb ?_ (by simp [size]; omega)) ?_ (by simp [size, hlb.eq]; omega)
            · refine Or.inr ⟨?_, ?_⟩
              · simp [size]
                omega
              · simp [size, delta] at *
                omega
            · refine Or.inr ⟨?_, ?_⟩
              · simp [size, delta] at *
                omega
              · simp [size, delta, ratio] at *
                omega
          · rename_i rs _ _ _ _ hrb _ _ _ ls _ _ hdel _ _ _ _ lls _ _ _ _ lrs _ _ _ _ hlb hlr _ hrat
            -- I have a pen-and-paper proof of this
            sorry
        · exact False.elim'
        · exact False.elim'
      · refine .inner ‹_› ‹_› ?_ (by simp [size])
        rename_i hrb _ _ _ _ _ _ _ _ hlb hlr _ _
        rcases hlr with (hlr|⟨-, hlr⟩)
        · simp [size, delta] at *
          refine Or.inr ⟨?_, ?_⟩
          · rw [delta]
            assumption
          · rw [delta]
            have := hlb.pos
            have := hrb.pos
            omega
        · refine Or.inr ⟨?_, ?_⟩
          · simp [size]
            omega
          · simp [delta] at *
            omega



@[inline] def balanceR (k : α) (v : β k) (l r : Raw α β) (hlb : Balanced l) (hrb : Balanced r) : Raw α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf) (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        if rls < ratio * rrs then .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
        else .inner (1 + rs) rlk rlv (.inner (1 + rll.size) k v .leaf rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if hrsd : rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | leaf, _ => False.elim (by
              rw [delta] at hrsd
              have : 3 < rs := by have := hlb.pos; omega
              have := hrb.size_leaf_left
              omega)
          | _, leaf => False.elim (by
              rw [delta] at hrsd
              have : 3 < rs := by have := hlb.pos; omega
              have := hrb.size_leaf_right
              omega)
        else .inner (1 + ls + rs) k v l r


@[specialize] def insert (cmp : α → α → Ordering) (k : α) (v : β k) : Raw α β → Raw α β
| leaf => .inner 1 k v .leaf .leaf
| inner sz ky y l r => match cmp k ky with
    | .lt => balanceL ky y (insert cmp k v l) r sorry sorry sorry
    | .eq => .inner sz k v l r
    | .gt => balanceR ky y l (insert cmp k v r) sorry sorry

@[specialize] def get? (cmp : α → α → Ordering) (h : ∀ {k₁ k₂}, cmp k₁ k₂ = .eq → k₁ = k₂) (k : α) : Raw α β → Option (β k)
| leaf => none
| inner _ ky y l r =>
    match hc : cmp k ky with
    | .lt => get? cmp h k l
    | .gt => get? cmp h k r
    | .eq => some (cast (congrArg β (h hc).symm) y)

@[specialize] def insertionPoint (cmp : α → α → Ordering) (k : α) (t : Raw α β) : Nat :=
  go 0 t
where
  @[specialize] go (sofar : Nat) : Raw α β → Nat
  | leaf => sofar
  | inner _ ky _ l r =>
    match cmp k ky with
    | .lt => go sofar l
    | .eq => sofar + size l
    | .gt => go (sofar + 1 + size l) r

def depth : Raw α β → Nat
| leaf => 0
| inner _ _ _ l r => 1 + max l.depth r.depth

def toList : Raw α β → List ((a : α) × β a)
| leaf => []
| inner _ k v l r => l.toList ++ [⟨k, v⟩] ++ r.toList
/-
theorem toList_balanceR (k : α) (v : β k) (l r : Raw α β) : (balanceR k v l r).toList = (Raw.inner 0 k v l r).toList := by
  rw [balanceR]
  split
  · split
    · simp only [toList]
    · simp only [toList]
    · simp only [toList]
      ac_rfl
    · simp [toList]
      -- Here we need to know that the anonymously introduced subtrees are leaves
      sorry
    · split
      · simp [toList]
      · simp [toList]
  · split
    · simp [toList]
    · split
      · split
        · split
          · simp [toList]
          · simp [toList]
        · sorry
      · simp [toList] -/

end Raw

end DOrderedTree

end Std
