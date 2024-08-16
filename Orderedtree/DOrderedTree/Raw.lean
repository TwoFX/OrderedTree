/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
universe u v

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

def AlmostBalancedL (left right : Nat) : Prop :=
  left + right ≤ 2 ∨ (left ≤ delta * right + 1 ∧ right + delta ≤ delta * left)

inductive Balanced : Raw α β → Prop
| leaf : Balanced leaf
| inner {size k v l r} : Balanced l → Balanced r → BalancedAtRoot l.size r.size → size = 1 + l.size + r.size → Balanced (inner size k v l r)

theorem Balanced.pos {size k v} {l r : Raw α β} : (Raw.inner size k v l r).Balanced → 0 < size
| inner _ _ _ h => by omega

theorem Balanced.eq {size k v} {l r : Raw α β} : (Raw.inner size k v l r).Balanced → size = 1 + l.size + r.size
| inner _ _ _ h => h

theorem Balanced.size_leaf_left {size k v} {r : Raw α β} : (Raw.inner size k v Raw.leaf r).Balanced → size ≤ 3
| inner _ _ h hs => by
    rcases h with (h|⟨-, h⟩)
    all_goals
    · rw [size_leaf] at h
      rw [hs, size_leaf]
      omega

theorem Balanced.size_leaf_right {size k v} {l : Raw α β} : (Raw.inner size k v l Raw.leaf).Balanced → size ≤ 3
| inner _ _ h hs => by
    rcases h with (h|⟨h, -⟩)
    all_goals
    · rw [size_leaf] at h
      rw [hs, size_leaf]
      omega

instance : Inhabited (Raw α β) where
  default := .leaf


@[inline] def balanceL (k : α) (v : β k) (l r : Raw α β) (hrb : Balanced r) (hlb : Balanced l) (hlr : AlmostBalancedL l.size r.size) : Raw α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | l@(inner _ _ _ .leaf .leaf) => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
    | inner ls lk lv ll@(.inner lls _ _ _ _) lr@(.inner lrs lrk lrv lrl lrr) =>
        if lrs < ratio * lls then .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v lr .leaf)
        else .inner (1 + ls) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl) (.inner (1 + lrr.size) k v lrr .leaf)
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
    | .lt => balanceL ky y (insert cmp k v l) r sorry sorry
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
