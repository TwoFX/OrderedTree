/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.List.Associative
import Lean.Elab.Tactic

set_option autoImplicit false

universe u v w

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

-- TODO: this doesn't really gain you anything over defining it to be `k ∈ keys l.toList`.

def toList : Raw α β → List ((a : α) × β a)
| leaf => []
| inner _ k v l r => l.toList ++ ⟨k, v⟩ :: r.toList

@[simp]
theorem toList_leaf : (Raw.leaf : Raw α β).toList = [] := rfl

@[simp]
theorem toList_inner {s k v l r} :
    (Raw.inner s k v l r : Raw α β).toList = l.toList ++ ⟨k, v⟩ :: r.toList := rfl

@[simp]
theorem toList_eq_nil {l : Raw α β} : l.toList = [] ↔ l = .leaf := by
  cases l <;> simp

def Mem (k : α) (l : Raw α β) : Prop :=
  k ∈ Std.DHashMap.Internal.List.keys l.toList

instance : Membership α (Raw α β) where
  mem l k := Mem k l

theorem mem_def {k : α} {l : Raw α β} : k ∈ l ↔ k ∈ Std.DHashMap.Internal.List.keys l.toList := Iff.rfl

@[simp]
theorem not_mem_leaf {k : α} : ¬k ∈ (Raw.leaf : Raw α β) := by
  rintro (_|_|_)

@[simp]
theorem mem_inner_iff {k : α} {s k' v l r} :
    k ∈ (Raw.inner s k' v l r : Raw α β) ↔ k ∈ l ∨ k = k' ∨ k ∈ r := by
  simp [mem_def, Std.DHashMap.Internal.List.keys_eq_map]

inductive Ordered [Ord α] : Raw α β → Prop where
  | leaf : Ordered leaf
  | inner {s k v l r} : Ordered l → Ordered r →
      (∀ k' ∈ l, compare k' k = .lt) → (∀ k' ∈ r, compare k k' = .lt) → Ordered (Raw.inner s k v l r)

attribute [simp] Ordered.leaf

theorem Ordered.left [Ord α] {s k v l r} : (Raw.inner s k v l r : Raw α β).Ordered → l.Ordered
| inner h _ _ _ => h

theorem Ordered.right [Ord α] {s k v l r} : (Raw.inner s k v l r : Raw α β).Ordered → r.Ordered
| inner _ h _ _ => h

theorem Ordered.compare_left [Ord α] {s k v l r k'} : (Raw.inner s k v l r : Raw α β).Ordered → k' ∈ l → compare k' k = .lt
| inner _ _ h _, h' => h _ h'

theorem Ordered.compare_right [Ord α] {s k v l r k'} : (Raw.inner s k v l r : Raw α β).Ordered → k' ∈ r → compare k k' = .lt
| inner _ _ _ h, h' => h _ h'

theorem Ordered.compare_left_right [Ord α] [TransOrd α] {s k v l r k' k''} (h : (Raw.inner s k v l r : Raw α β).Ordered) (h' : k' ∈ l) (h'' : k'' ∈ r) : compare k' k'' = .lt :=
  lt_trans (h.compare_left h') (h.compare_right h'')

@[simp]
theorem ordered_inner_leaf_leaf [Ord α] {s k v} : (Raw.inner s k v .leaf .leaf : Raw α β).Ordered := by
  apply Ordered.inner <;> simp

@[simp] theorem size_leaf : (leaf : Raw α β).size = 0 := rfl
@[simp] theorem size_inner {sz k v l r} : (Raw.inner sz k v l r : Raw α β).size = sz := rfl

def BalancedAtRoot (left right : Nat) : Prop :=
  left + right ≤ 1 ∨ (left ≤ delta * right ∧ right ≤ delta * left)

theorem BalancedAtRoot.symm {left right : Nat} : BalancedAtRoot left right → BalancedAtRoot right left := by
  simp only [BalancedAtRoot]
  omega

theorem balancedAtRoot_leaf_leaf : BalancedAtRoot (leaf : Raw α β).size (leaf : Raw α β).size :=
  Or.inl (by simp)

inductive Balanced : Raw α β → Prop
| leaf : Balanced leaf
| inner {size k v l r} : Balanced l → Balanced r → BalancedAtRoot l.size r.size → size = 1 + l.size + r.size → Balanced (inner size k v l r)

theorem balanced_inner_iff {sz k v l r} : Balanced (Raw.inner sz k v l r : Raw α β) ↔ Balanced l ∧ Balanced r ∧ BalancedAtRoot l.size r.size ∧ sz = 1 + l.size + r.size :=
  ⟨by rintro (_|⟨h₁, h₂, h₃, h₄⟩); exact ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => .inner h₁ h₂ h₃ h₄⟩

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

theorem Balanced.update {sz k k' v v' l r} : (Raw.inner sz k v l r : Raw α β).Balanced → (Raw.inner sz k' v' l r : Raw α β).Balanced
| inner l r h₁ h₂ => inner l r h₁ h₂

instance : Inhabited (Raw α β) where
  default := .leaf

abbrev BalanceLPrecond (left right : Nat) :=
  BalancedAtRoot left right ∨ (1 ≤ left ∧ BalancedAtRoot (left - 1) right)

@[inline] def balanceL (k : α) (v : β k) (l r : Raw α β) (hrb : Balanced r) (hlb : Balanced l) --(hq : BalancedAtRoot (l.size - 1) r.size)
    (hlr : BalanceLPrecond l.size r.size) : Raw α β :=
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
          dsimp only [BalanceLPrecond, BalancedAtRoot] at hlr
          simp [size] at hlr
          have := hlb.left.pos
          have := hlb.right.pos
          have := hlb.eq
          simp [size] at this
          simp only [delta] at *
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

theorem False.elim₂ {h : False} {n : Nat} : (h.elim : Raw α β).size = n :=
  h.elim

open Lean Meta Elab Tactic

elab "split_and" : tactic => liftMetaTactic fun mvarId => do
  let hyps ← getPropHyps
  for hyp in hyps do
    let t ← instantiateMVars (← hyp.getType)
    -- dbg_trace "{t}"
    if let .app (.app (.const `And _) _) _ := t then
      return (← runTactic mvarId (← `(tactic| cases $(Lean.mkIdent (← hyp.getUserName)):term))).1
  throwError "no matching hypothesis found"

-- set_option trace.profiler.threshold 50
-- set_option trace.profiler true in
-- set_option profiler true in
theorem balanced_balanceL {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr : BalanceLPrecond l.size r.size} :
    (balanceL k v l r hrb hlb hlr).Balanced := by
  simp only [balanceL.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
    repeat' apply And.intro
  all_goals
    try apply Balanced.leaf
    try apply False.elim'
    try assumption
  all_goals
    omega

@[simp] theorem size_balanceL {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr : BalanceLPrecond l.size r.size} :
    (balanceL k v l r hrb hlb hlr).size = 1 + l.size + r.size := by
  simp only [balanceL.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
  all_goals
    try apply False.elim₂
    try omega

 def balanceR (k : α) (v : β k) (l r : Raw α β) (hlb : Balanced l) (hrb : Balanced r) (hlr : BalanceLPrecond r.size l.size) : Raw α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf) (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        False.elim (by
          dsimp only [BalanceLPrecond, BalancedAtRoot] at hlr
          simp [size] at hlr
          have := hrb.left.pos
          have := hrb.right.pos
          have := hrb.eq
          simp [size] at this
          simp only [delta] at *
          omega)
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

theorem balanced_balanceR {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr : BalanceLPrecond r.size l.size} :
    (balanceR k v l r hlb hrb hlr).Balanced := by
  simp only [balanceR.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
    repeat' apply And.intro
  all_goals
    try apply Balanced.leaf
    try apply False.elim'
    try assumption
  all_goals
    omega

@[simp] theorem size_balanceR {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr : BalanceLPrecond r.size l.size} :
    (balanceR k v l r hlb hrb hlr).size = 1 + l.size + r.size := by
  simp only [balanceR.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
  all_goals
    try apply False.elim₂
    try omega

/-- Slower version of `balanceR` that has to handle additional cases. -/
@[inline] def balanceRErase (k : α) (v : β k) (l r : Raw α β) (hlb : Balanced l) (hrb : Balanced r) (hlr : BalancedAtRoot (1 + l.size) r.size ∨ BalancedAtRoot l.size r.size) : Raw α β :=
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

theorem balanced_balanceRErase {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr} :
    (balanceRErase k v l  r hlb hrb hlr).Balanced := by
  simp only [balanceRErase.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
    -- try simp [Balanced.leaf, *]
    repeat' apply And.intro
  all_goals
    try apply Balanced.leaf
    try apply False.elim'
    try assumption
  all_goals
    omega

@[simp] theorem size_balanceRErase {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr} :
    (balanceRErase k v l r hlb hrb hlr).size = 1 + l.size + r.size := by
  simp only [balanceRErase.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
  all_goals
    try apply False.elim₂
    try omega

@[inline] def balanceLErase (k : α) (v : β k) (l r : Raw α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalancedAtRoot l.size (r.size + 1) ∨ BalancedAtRoot l.size r.size) : Raw α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
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

theorem balanced_balanceLErase {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr} :
    (balanceLErase k v l r hlb hrb hlr).Balanced := by
  simp only [balanceLErase.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
    -- try simp [Balanced.leaf, *]
    repeat' apply And.intro
  all_goals
    try apply Balanced.leaf
    try apply False.elim'
    try assumption
  all_goals
    omega

@[simp] theorem size_balanceLErase {k : α} {v : β k} {l r : Raw α β} {hrb : Balanced r} {hlb : Balanced l} {hlr} :
    (balanceLErase k v l r hlb hrb hlr).size = 1 + l.size + r.size := by
  simp only [balanceLErase.eq_def]
  repeat' split
  all_goals
    simp [BalanceLPrecond, BalancedAtRoot, balanced_inner_iff, delta, ratio] at *
    repeat' split_and
  all_goals
    try apply False.elim₂
    try omega

theorem help (l r i : Nat) (h₁ : l ≤ i) (h₂ : i ≤ l + 1) (h₃ : l + r ≤ 1 ∨ (l ≤ 3 * r ∧ r ≤ 3 * l)) :
    (i + r ≤ 1 ∨ (i ≤ 3 * r ∧ r ≤ 3 * i)) ∨ (1 ≤ i ∧ (i - 1 + r ≤ 1 ∨ (i - 1 ≤ 3 * r ∧ r ≤ 3 * (i - 1)))) := by omega

theorem help' (l r i : Nat) (h₁ : r ≤ i) (h₂ : i ≤ r + 1) (h₃ : l + r ≤ 1 ∨ (l ≤ 3 * r ∧ r ≤ 3 * l)) :
    (i + l ≤ 1 ∨ (i ≤ 3 * l ∧ l ≤ 3 * i)) ∨ (1 ≤ i ∧ (i - 1 + l ≤ 1 ∨ (i - 1 ≤ 3 * l ∧ l ≤ 3 * (i - 1)))) := by omega

@[specialize] def insert [Ord α] (k : α) (v : β k) : (q : { r : Raw α β // r.Balanced }) → { r : Raw α β // r.Balanced ∧ q.1.size ≤ r.size ∧ r.size ≤ q.1.size + 1 }
| ⟨leaf, h⟩ => ⟨.inner 1 k v .leaf .leaf, ⟨balanced_singleton, by simp, by simp⟩⟩
| ⟨inner sz ky y l r, h⟩ =>
  match compare k ky with
  | .lt =>
      let i := insert k v ⟨l, h.left⟩
      ⟨balanceL ky y i.1 r h.right i.2.1 (by
          have := i.2.2.1
          have := i.2.2.2
          rw [balanced_inner_iff] at h
          simp [delta, ratio, balanced_inner_iff, BalancedAtRoot, BalanceLPrecond] at *
          repeat' split_and
          apply help <;> assumption
          ), ⟨balanced_balanceL,
        by simp; have := i.2.2.1; have := i.2.2.2; have := h.eq; simp_all,
        by simp; have := i.2.2.1; have := i.2.2.2; have := h.eq; simp_all; omega⟩⟩
  | .eq => ⟨.inner sz k v l r, ⟨h.update, Nat.le_refl _, by simp⟩⟩
  | .gt =>
      let i := insert k v ⟨r, h.right⟩
      ⟨balanceR ky y l i.1 h.left i.2.1 (by
          have := i.2.2.1
          have := i.2.2.2
          rw [balanced_inner_iff] at h
          simp [delta, ratio, balanced_inner_iff, BalancedAtRoot, BalanceLPrecond] at *
          repeat' split_and
          apply help' <;> assumption
      ), ⟨balanced_balanceR,
        by simp; have := i.2.2.1; have := i.2.2.2; have := h.eq; simp_all,
        by simp; have := i.2.2.1; have := i.2.2.2; have := h.eq; simp_all; omega⟩⟩

def insertWithoutRebalancing [Ord α] (k : α) (v : β k) : Raw α β → Raw α β
| leaf => .inner 1 k v .leaf .leaf
| inner sz ky y l r =>
  match compare k ky with
  | .lt => .inner (sz + 1) ky y (insertWithoutRebalancing k v l) r
  | .eq => .inner sz k v l r
  | .gt => .inner (sz + 1) ky y l (insertWithoutRebalancing k v r)

variable (α β) in
structure RawView where
  k : α
  v : β k
  tree : Raw α β

def RawView.p : RawView α β → (k : α) × β k
  | ⟨k, v, _⟩ => ⟨k, v⟩

variable (α β) in
structure View (n : Nat) where
  raw : RawView α β
  balanced : raw.tree.Balanced
  hsz : raw.tree.size = n

def minView (k : α) (v : β k) (l r : Raw α β) (hl : l.Balanced) (hr : r.Balanced) (h : BalancedAtRoot l.size r.size) : View α β (l.size + r.size) :=
  match l with
  | leaf => ⟨⟨k, v, r⟩, hr, by simp⟩
  | inner _ k' v' l' r' =>
      let d := minView k' v' l' r' hl.left hl.right hl.root
      ⟨⟨d.raw.p.1, d.raw.p.2, balanceRErase k v d.raw.tree r d.balanced hr (Or.inl <| by rwa [hl.eq, size_inner, Nat.add_assoc, ← d.hsz] at h)⟩,
        balanced_balanceRErase, by simp [hl.eq, d.hsz, Nat.add_assoc]⟩

def maxView (k : α) (v : β k) (l r : Raw α β) (hl : l.Balanced) (hr : r.Balanced) (h : BalancedAtRoot l.size r.size) : View α β (l.size + r.size) :=
  match r with
  | leaf => ⟨⟨k, v, l⟩, hl, by simp⟩
  | inner _ k' v' l' r' =>
      let d := maxView k' v' l' r' hr.left hr.right hr.root
      ⟨⟨d.raw.k, d.raw.v, balanceLErase k v l d.raw.tree hl d.balanced (Or.inl <| by rwa [hr.eq, size_inner, Nat.add_assoc, ← d.hsz, Nat.add_comm] at h)⟩,
        balanced_balanceLErase, by simp [hr.eq, d.hsz]; omega⟩

def glue (l r : Raw α β) (hl : l.Balanced) (hr : r.Balanced) (h : BalancedAtRoot l.size r.size) : Raw α β :=
  match l with
  | .leaf => r
  | l@hl₀:(.inner sz k v l' r') =>
    match r with
    | .leaf => l
    | r@hr₀:(.inner sz' k' v' l'' r'') =>
      if sz < sz' then
        let d := minView k' v' l'' r'' hr.left hr.right hr.root
        balanceLErase d.raw.p.1 d.raw.p.2 l d.raw.tree (hl₀ ▸ hl) d.balanced (Or.inl <| by simp [hl.eq, hr.eq] at h; simp [hl₀, hl.eq, d.hsz]; rwa [Nat.add_comm _ 1, ← Nat.add_assoc])
      else
        let d := maxView k v l' r' hl.left hl.right hl.root
        balanceRErase d.raw.p.1 d.raw.p.2 d.raw.tree r d.balanced (hr₀ ▸ hr) (Or.inl <| by simp [hl.eq, hr.eq] at h; simp [hr₀, hr.eq, d.hsz]; rwa [← Nat.add_assoc])

theorem balanced_glue {l r : Raw α β} {hl hr h} : (glue l r hl hr h).Balanced := by
  simp only [glue]
  repeat' split
  · assumption
  · assumption
  · exact balanced_balanceLErase
  · exact balanced_balanceRErase

@[simp]
theorem size_glue {l r : Raw α β} {hl hr h} : (glue l r hl hr h).size = l.size + r.size := by
  simp only [glue]
  repeat' split
  · simp
  · simp
  · sorry
  · sorry

def erase [Ord α] (l : Raw α β) (k : α) (h : l.Balanced) : { m : Raw α β // m.Balanced ∧ (m.size = l.size ∨ m.size + 1 = l.size) } :=
  match l with
  | leaf => ⟨.leaf, Balanced.leaf, by simp⟩
  | inner sz k' v' l r =>
    match compare k k' with
    | .lt => sorry
    | .gt => sorry
    | .eq => ⟨glue l r h.left h.right h.root, balanced_glue, by simp [h.eq]; ac_rfl⟩


def minViewRaw (k : α) (v : β k) (l r : Raw α β) : RawView α β :=
  match l with
  | leaf => ⟨k, v, r⟩
  | inner _ k' v' l' r' =>
      let d := minViewRaw k' v' l' r'
      ⟨d.p.1, d.p.2, .inner (1 + d.tree.size + r.size) k v d.tree r⟩

@[simp]
theorem toList_minViewRaw_tree {k : α} {v : β k} {l r : Raw α β} :
    ⟨(minViewRaw k v l r).p.1, (minViewRaw k v l r).p.2⟩ :: (minViewRaw k v l r).tree.toList = l.toList ++ ⟨k, v⟩ :: r.toList := by
  induction k, v, l, r using minViewRaw.induct
  · simp [minViewRaw, RawView.p]
  · rename_i ih
    simp only [minViewRaw, toList_inner]
    rw [← List.cons_append]
    simp only [RawView.p] at ih
    simp [RawView.p, ih]

def maxViewRaw (k : α) (v : β k) (l r : Raw α β) : RawView α β :=
  match r with
  | leaf => ⟨k, v, l⟩
  | inner _ k' v' l' r' =>
      let d := maxViewRaw k' v' l' r'
      ⟨d.k, d.v, .inner (1 + l.size + d.tree.size) k v l d.tree⟩

@[simp]
theorem toList_maxViewRaw_tree {k : α} {v : β k} {l r : Raw α β} :
    (maxViewRaw k v l r).tree.toList ++ [⟨(maxViewRaw k v l r).p.1, (maxViewRaw k v l r).p.2⟩] = l.toList ++ ⟨k, v⟩ :: r.toList := by
  induction k, v, l, r using maxViewRaw.induct
  · simp_all [maxViewRaw, RawView.p]
  · rename_i ih
    simp only [RawView.p] at ih
    simp [RawView.p, ih, maxViewRaw]

theorem minViewRaw_mem {k : α} {v : β k} {l r : Raw α β} {sz : Nat} : (minViewRaw k v l r).p.1 ∈ inner sz k v l r := by
  induction k, v, l, r using minViewRaw.induct <;> simp_all [minViewRaw, RawView.p]

theorem of_mem_minViewRaw {k : α} {v : β k} {l r : Raw α β} {k' : α} : k' ∈ (minViewRaw k v l r).tree → k' = k ∨ k' ∈ l ∨ k' ∈ r := by
  induction k, v, l, r using minViewRaw.induct
  · simpa only [minViewRaw, not_mem_leaf, false_or] using Or.inr
  · rename_i v r sz ky y l' r' ih
    simp [minViewRaw]
    rintro (hk'|rfl|hk')
    · rcases ih hk' with (rfl|hk'|hk') <;> simp_all
    · simp
    · simp_all

theorem compare_minViewRaw [Ord α] [TransOrd α] {k : α} {v : β k} {l r : Raw α β} {k' : α} (hk' : k' ∈ (minViewRaw k v l r).tree) {sz : Nat} (h : (inner sz k v l r).Ordered) : compare (minViewRaw k v l r).k k' = .lt := by
  induction k, v, l, r using minViewRaw.induct generalizing sz
  · simp_all [minViewRaw]
    exact h.compare_right hk'
  · rename_i k₀ v r sz' ky y l' r' ih
    simp_all [minViewRaw]
    rcases hk' with (hk'|rfl|hk')
    · exact ih hk' h.left
    · exact h.compare_left minViewRaw_mem
    · exact h.compare_left_right minViewRaw_mem hk'

theorem ordered_minViewRaw [Ord α] {k : α} {v : β k} {l r : Raw α β} (hl : l.Ordered) (hr : r.Ordered) (hlk : ∀ k' ∈ l, compare k' k = .lt) (hrk : ∀ k' ∈ r, compare k k' = .lt) :
    Ordered (minViewRaw k v l r).tree := by
  induction k, v, l, r using minViewRaw.induct
  · simpa [minViewRaw]
  · rename_i k' v' r sz ky y l r ih
    simp only [minViewRaw]
    refine Ordered.inner ?_ hr ?_ ?_
    · apply ih hl.left hl.right
      · exact fun k' hk' => hl.compare_left hk'
      · exact fun k' hk' => hl.compare_right hk'
    · intro k₀ hk₀
      rcases of_mem_minViewRaw hk₀ with (rfl|hk₀|hk₀) <;> exact hlk _ (by simp_all)
    · exact hrk

theorem ordered_minViewRaw_of_ordered_inner [Ord α] {k : α} {v : β k} {l r : Raw α β} {sz: Nat} (h : (inner sz k v l r).Ordered) : (minViewRaw k v l r).tree.Ordered :=
  ordered_minViewRaw h.left h.right (fun _ hk => h.compare_left hk) (fun _ hk => h.compare_right hk)

theorem maxViewRaw_mem {k : α} {v : β k} {l r : Raw α β} {sz : Nat} : (maxViewRaw k v l r).k ∈ inner sz k v l r := by
  induction k, v, l, r using maxViewRaw.induct <;> simp_all [maxViewRaw]

theorem of_mem_maxViewRaw {k : α} {v : β k} {l r : Raw α β} {k' : α} : k' ∈ (maxViewRaw k v l r).tree → k' = k ∨ k' ∈ l ∨ k' ∈ r := by
  induction k, v, l, r using maxViewRaw.induct
  · simpa only [maxViewRaw, not_mem_leaf, or_false] using Or.inr
  · rename_i v r sz ky y l' r' ih
    simp [maxViewRaw]
    rintro (hk'|rfl|hk')
    · simp_all
    · simp
    · rcases ih hk' with (rfl|hk'|hk') <;> simp_all

theorem compare_maxViewRaw [Ord α] [TransOrd α] {k : α} {v : β k} {l r : Raw α β} {k' : α} (hk' : k' ∈ (maxViewRaw k v l r).tree) {sz : Nat} (h : (inner sz k v l r).Ordered) : compare k' (maxViewRaw k v l r).k = .lt := by
  induction k, v, l, r using maxViewRaw.induct generalizing sz
  · simp_all [maxViewRaw]
    exact h.compare_left hk'
  · rename_i k₀ v r sz' ky y l' r' ih
    simp_all [maxViewRaw]
    rcases hk' with (hk'|rfl|hk')
    · exact h.compare_left_right hk' maxViewRaw_mem
    · exact h.compare_right maxViewRaw_mem
    · exact ih hk' h.right

theorem ordered_maxViewRaw [Ord α] {k : α} {v : β k} {l r : Raw α β} (hl : l.Ordered) (hr : r.Ordered) (hlk : ∀ k' ∈ l, compare k' k = .lt) (hrk : ∀ k' ∈ r, compare k k' = .lt) :
    Ordered (maxViewRaw k v l r).tree := by
  induction k, v, l, r using maxViewRaw.induct
  · simpa [maxViewRaw]
  · rename_i k' v' r sz ky y l r ih
    simp only [maxViewRaw]
    refine Ordered.inner hl ?_ ?_ ?_
    · apply ih hr.left hr.right
      · exact fun k' hk' => hr.compare_left hk'
      · exact fun k' hk' => hr.compare_right hk'
    · exact hlk
    · intro k₀ hk₀
      rcases of_mem_maxViewRaw hk₀ with (rfl|hk₀|hk₀) <;> exact hrk _ (by simp_all)

theorem ordered_maxViewRaw_of_ordered_inner [Ord α] {k : α} {v : β k} {l r : Raw α β} {sz: Nat} (h : (inner sz k v l r).Ordered) : (maxViewRaw k v l r).tree.Ordered :=
  ordered_maxViewRaw h.left h.right (fun _ hk => h.compare_left hk) (fun _ hk => h.compare_right hk)

def glueRaw (l r : Raw α β) : Raw α β :=
  match l with
  | .leaf => r
  | l@(.inner sz k v l' r') =>
    match r with
    | .leaf => l
    | r@(.inner sz' k' v' l'' r'') =>
      if sz < sz' then
        let d := minViewRaw k' v' l'' r''
        .inner (1 + l.size + d.tree.size) d.p.1 d.p.2 l d.tree
      else
        let d := maxViewRaw k v l' r'
        .inner (1 + d.tree.size + r.size) d.p.1 d.p.2 d.tree r

def updateAtKey [Ord α] (k : α) (f : Option ((a : α) × β a) → Option ((a : α) × β a)) : Raw α β → Raw α β
| leaf => match f none with
          | none => .leaf
          | some ⟨k', v'⟩ => .inner 1 k' v' .leaf .leaf
| inner sz ky y l r =>
  match compare k ky with
  | .lt =>
      let newL := updateAtKey k f l
      .inner (1 + newL.size + r.size) ky y newL r
  | .eq => match f (some ⟨ky, y⟩) with
           | none => glueRaw l r
           | some ⟨ky', y'⟩ => .inner sz ky' y' l r
  | .gt =>
      let newR := updateAtKey k f r
      .inner (1 + l.size + newR.size) ky y l newR

def insertₘ [Ord α] (k : α) (v : β k) : Raw α β → Raw α β :=
  updateAtKey k (fun _ => some ⟨k, v⟩)

inductive Sized : Raw α β → Prop where
  | leaf : Sized leaf
  | inner {sz ky y l r} : Sized l → Sized r → sz = 1 + l.size + r.size → Sized (Raw.inner sz ky y l r : Raw α β)

theorem Sized.left {sz ky y l r} : (Raw.inner sz ky y l r : Raw α β).Sized → l.Sized
  | inner h _ _ => h

theorem Sized.right {sz ky y l r} : (Raw.inner sz ky y l r : Raw α β).Sized → r.Sized
  | inner _ h _ => h

theorem Sized.eq {sz ky y l r} : (Raw.inner sz ky y l r : Raw α β).Sized → (Raw.inner sz ky y l r).size = 1 + l.size + r.size
  | inner _ _ h => h

variable (α β) in
inductive ExplorationStep where
  /-- Needle was less than key at this node: return key-value pair and unexplored right subtree,
      recusion will continue in left subtree. -/
  | lt : (a : α) → β a → Raw α β → ExplorationStep
  /-- Needle was equal to key at this node: return key-value pair and both unexplored subtrees,
      recursion will terminate. -/
  | eq : Raw α β → (a : α) → β a → Raw α β → ExplorationStep
  /-- Needle was larger than key at this node: return key-value pair and unexplored left subtree,
      recusion will containue in right subtree. -/
  | gt : Raw α β → (a : α) → β a → ExplorationStep

def explore {γ : Type w} [Ord α] (k : α) (init : γ)
    (inner : γ → ExplorationStep α β → γ) : Raw α β → γ
| .leaf => init
| .inner _ ky y l r => match compare k ky with
    | .lt => explore k (inner init <| .lt ky y r) inner l
    | .eq => inner init <| .eq l ky y r
    | .gt => explore k (inner init <| .gt l ky y) inner r

/-- The smallest element of `l` that is not less than `k`. -/
def lowerBound?ₘ [Ord α] (k : α) (l : Raw α β) : Option ((a : α) × β a) :=
  explore k none (fun sofar step =>
    match step with
    | .lt ky y _ => some ⟨ky, y⟩
    | .eq _ ky y _ => some ⟨ky, y⟩
    | .gt _ _ _ => sofar) l

/-- The smallest element of `l` that is not less than `k`. -/
def lowerBound? [Ord α] (k : α) : Raw α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Raw α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .lt => go (some ⟨ky, y⟩) l
    | .eq => some ⟨ky, y⟩
    | .gt => go best r

theorem lowerBound?_eq_lowerBound?ₘ [Ord α] {k : α} {l : Raw α β} : l.lowerBound? k = l.lowerBound?ₘ k := by
  rw [lowerBound?, lowerBound?ₘ]
  suffices ∀ o, lowerBound?.go k o l = explore k o _ l from this none
  intro o
  induction l generalizing o with
  | leaf => simp [explore, lowerBound?.go]
  | inner s ky y l r ih₁ ih₂ =>
    rw [lowerBound?.go, explore]
    cases compare k ky with
    | lt => simp [ih₁]
    | eq => simp
    | gt => simp [ih₂]

@[specialize] def get? [Ord α] (h : ∀ {k₁ k₂ : α}, compare k₁ k₂ = .eq → k₁ = k₂) (k : α) : Raw α β → Option (β k)
| leaf => none
| inner _ ky y l r =>
  match hc : compare k ky with
  | .lt => get? h k l
  | .gt => get? h k r
  | .eq => some (cast (congrArg β (h hc).symm) y)

def getEntry? [Ord α] (k : α) : Raw α β → Option ((a : α) × β a)
| leaf => none
| inner _ ky y l r =>
  match compare k ky with
  | .lt => getEntry? k l
  | .gt => getEntry? k r
  | .eq => some ⟨ky, y⟩

/-- Counts the number of elements that are strictly less than `k` -/
@[specialize] def insertionPoint [Ord α] (k : α) (t : Raw α β) : Nat :=
  go 0 t
where
  @[specialize] go (sofar : Nat) : Raw α β → Nat
  | leaf => sofar
  | inner _ ky _ l r =>
    match compare k ky with
    | .lt => go sofar l
    | .eq => sofar + size l
    | .gt => go (sofar + 1 + size l) r

def insertionPointₘ [Ord α] (k : α) (l : Raw α β) : Nat :=
  explore k 0 (fun sofar step =>
    match step with
    | .lt _ _ _ => sofar
    | .eq l _ _ _ => sofar + l.size
    | .gt l _ _ => sofar + 1 + l.size) l

theorem insertionPoint_eq_insertionPointₘ [Ord α] {k : α} {l : Raw α β} :
    l.insertionPoint k = l.insertionPointₘ k := by
  rw [insertionPoint, insertionPointₘ]
  suffices ∀ n, insertionPoint.go k n l = explore k n _ l from this 0
  intro n
  induction l generalizing n with
  | leaf => simp [explore, insertionPoint.go]
  | inner s ky y l r ih₁ ih₂ =>
    rw [insertionPoint.go, explore]
    cases compare k ky with
    | lt => simp [ih₁]
    | eq => simp
    | gt => simp [ih₂]

def depth : Raw α β → Nat
| leaf => 0
| inner _ _ _ l r => 1 + max l.depth r.depth

theorem Sized.length_toList {l : Raw α β} (hl : l.Sized) : l.toList.length = l.size := by
  induction l with
  | leaf => simp
  | inner sz _ _ l r ih₁ ih₂ =>
    simp only [toList_inner, List.length_append, ih₁ hl.left, List.length_cons, ih₂ hl.right, hl.eq]
    ac_rfl

theorem False.elim₃ {h : False} {l} : (h.elim : Raw α β).toList = l :=
  h.elim

theorem bla {α : Type u} (a b : α) (l₁ l₂ : List α) : [a, b] = l₁ ++ a :: (l₂ ++ [b]) ↔ l₁ = [] ∧ l₂ = [] := by
  cases l₁ <;> cases l₂
  · simp
  · simp
  · simp
    rintro rfl
    apply mt (congrArg List.length)
    simp
  · simp
    rintro rfl
    apply mt (congrArg List.length)
    simp
    omega

@[simp]
theorem toList_balanceL (k : α) (v : β k) (l r : Raw α β) (h₁ h₂ h₃) : (balanceL k v l r h₁ h₂ h₃).toList = l.toList ++ ⟨k, v⟩ :: r.toList := by
  rw [balanceL.eq_def]
  repeat' split
  all_goals simp
  all_goals try apply False.elim₃
  simp_all [bla, BalanceLPrecond, BalancedAtRoot, balanced_inner_iff]
  repeat' split_and
  exact ⟨Balanced.size_eq_zero ‹_› (by omega), Balanced.size_eq_zero ‹_› (by omega)⟩

@[simp]
theorem toList_balanceLErase (k : α) (v : β k) (l r : Raw α β) (h₁ h₂ h₃) : (balanceLErase k v l r h₁ h₂ h₃).toList = l.toList ++ ⟨k, v⟩ :: r.toList := by
  rw [balanceLErase.eq_def]
  repeat' split
  all_goals simp
  all_goals try apply False.elim₃
  simp_all [bla, BalanceLPrecond, BalancedAtRoot, balanced_inner_iff]
  repeat' split_and
  exact ⟨Balanced.size_eq_zero ‹_› (by omega), Balanced.size_eq_zero ‹_› (by omega)⟩

@[simp]
theorem toList_balanceR (k : α) (v : β k) (l r : Raw α β) (h₁ h₂ h₃) : (balanceR k v l r h₁ h₂ h₃).toList = l.toList ++ ⟨k, v⟩ :: r.toList := by
  rw [balanceR.eq_def]
  repeat' split
  all_goals simp
  all_goals try apply False.elim₃
  simp_all [bla, BalanceLPrecond, BalancedAtRoot, balanced_inner_iff]
  repeat' split_and
  exact ⟨Balanced.size_eq_zero ‹_› (by omega), Balanced.size_eq_zero ‹_› (by omega)⟩

@[simp]
theorem toList_balanceRErase (k : α) (v : β k) (l r : Raw α β) (h₁ h₂ h₃) : (balanceRErase k v l r h₁ h₂ h₃).toList = l.toList ++ ⟨k, v⟩ :: r.toList := by
  rw [balanceRErase.eq_def]
  repeat' split
  all_goals simp
  all_goals try apply False.elim₃
  simp_all [bla, BalanceLPrecond, BalancedAtRoot, balanced_inner_iff]
  repeat' split_and
  exact ⟨Balanced.size_eq_zero ‹_› (by omega), Balanced.size_eq_zero ‹_› (by omega)⟩

@[simp]
theorem minView_raw_tree_toList {k : α} {v : β k} {l r : Raw α β} {hl hr hlr} : (minView k v l r hl hr hlr).raw.tree.toList = (minViewRaw k v l r).tree.toList := by
  induction k, v, l, r using minViewRaw.induct
  · simp [minView, minViewRaw]
  · rename_i k' v' r size k'' v'' l' r' ih
    simp [minView, minViewRaw, ih]

@[simp]
theorem minView_raw_p {k : α} {v : β k} {l r : Raw α β} {hl hr hlr} : (minView k v l r hl hr hlr).raw.p = (minViewRaw k v l r).p := by
  induction k, v, l, r using minViewRaw.induct
  · simp [minView, minViewRaw]
  · rename_i k' v' r size k'' v'' l' r' ih
    simp [minView, minViewRaw, ih, RawView.p]
    exact ih

@[simp]
theorem maxView_raw_tree_toList {k : α} {v : β k} {l r : Raw α β} {hl hr hlr} : (maxView k v l r hl hr hlr).raw.tree.toList = (maxViewRaw k v l r).tree.toList := by
  induction k, v, l, r using maxViewRaw.induct
  · simp [maxView, maxViewRaw]
  · rename_i k' v' r size k'' v'' l' r' ih
    simp [maxView, maxViewRaw, ih]

@[simp]
theorem maxView_raw_p {k : α} {v : β k} {l r : Raw α β} {hl hr hlr} : (maxView k v l r hl hr hlr).raw.p = (maxViewRaw k v l r).p := by
  induction k, v, l, r using maxViewRaw.induct
  · simp [maxView, maxViewRaw]
  · rename_i k' v' r size k'' v'' l' r' ih
    simp [maxView, maxViewRaw, ih, RawView.p]
    exact ih

@[simp]
theorem toList_glue_eq_toList_glueRaw {l r : Raw α β} {h₁ h₂ h₃} : (glue l r h₁ h₂ h₃).toList = (glueRaw l r).toList := by
  simp only [glue, glueRaw]
  cases l <;> cases r <;> simp <;> split
  · rw [minView_raw_p]
    simp
  · simp
    rw [maxView_raw_p]

theorem toList_insert_eq_toList_insertWithoutRebalancing [Ord α] {l : { l : Raw α β // l.Balanced}} {k : α} {v : β k} :
    (insert k v l).1.toList = (l.1.insertWithoutRebalancing k v).toList := by
  induction l using Raw.insert.induct k v
  · simp [insert, insertWithoutRebalancing]
  all_goals
    intros
    simp_all [insert, insertWithoutRebalancing, toList_balanceL, toList_balanceR]

theorem toList_insertWithoutRebalancing_eq_toList_insertₘ [Ord α] {l : Raw α β} {k : α} {v : β k} :
    (l.insertWithoutRebalancing k v).toList = (l.insertₘ k v).toList := by
  induction l using Raw.insertWithoutRebalancing.induct k v
    <;> simp_all [insertWithoutRebalancing, insertₘ, updateAtKey]

@[simp]
theorem toList_glueRaw {l r : Raw α β} : (glueRaw l r).toList = l.toList ++ r.toList := by
  simp only [glueRaw]
  repeat' split
  · simp
  · simp
  · simp
  · simp only [toList_inner]
    rw [List.append_cons, toList_maxViewRaw_tree]

@[simp]
theorem mem_glueRaw {l r : Raw α β} {k : α} : k ∈ glueRaw l r ↔ k ∈ l ∨ k ∈ r := by
  rw [mem_def, mem_def, mem_def, toList_glueRaw]
  simp [Std.DHashMap.Internal.List.keys_eq_map]

theorem ordered_glueRaw [Ord α] [TransOrd α] {l r : Raw α β} (hl : l.Ordered) (hr : r.Ordered) (hlr : ∀ k k', k ∈ l → k' ∈ r → compare k k' = .lt) :
    (glueRaw l r).Ordered := by
  simp only [glueRaw]
  repeat' split
  · exact hr
  · exact hl
  · rename_i r sz k' v' l₀ r₀ r₁ sz' k v l₂ r₂ hsz
    apply Ordered.inner
    · exact hl
    · exact ordered_minViewRaw_of_ordered_inner hr
    · simp only [mem_inner_iff]
      exact fun k₀ hk₀ => hlr _ _ (by simp_all) minViewRaw_mem
    · intro k₀ hk₀
      exact compare_minViewRaw hk₀ hr
  · rename_i r sz k' v' l₀ r₀ r₁ sz' k v l₂ r₂ hsz
    apply Ordered.inner
    · exact ordered_maxViewRaw_of_ordered_inner hl
    · exact hr
    · intro k₀ hk₀
      exact compare_maxViewRaw hk₀ hl
    · simp only [mem_inner_iff]
      exact fun k₀ hk₀ => hlr _ _ maxViewRaw_mem (by simp_all)

open Std.DHashMap.Internal.List

@[simp]
theorem keys_append {l l' : List ((a : α) × β a)} : keys (l ++ l') = keys l ++ keys l' := by
  simp [keys_eq_map]

theorem distinctKeys_append [BEq α] {l l' : List ((a : α) × β a)} : DistinctKeys (l ++ l') ↔
    DistinctKeys l ∧ DistinctKeys l' ∧ ∀ a ∈ keys l, ∀ b ∈ keys l', (a == b) = false := by
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨⟨h₁⟩, ⟨h₂⟩, h₃⟩ => ⟨?_⟩⟩
  · rw [keys_append, List.pairwise_append] at h
    exact ⟨⟨h.1⟩, ⟨h.2.1⟩, h.2.2⟩
  · rw [keys_append, List.pairwise_append]
    exact ⟨h₁, h₂, h₃⟩

attribute [local instance] beqOfOrd equivBEqOfTransOrd

theorem mem_keys_toList {l : Raw α β} {k : α} : k ∈ keys l.toList ↔ k ∈ l := by
  induction l <;> simp_all

theorem mem_of_mem_toList {l : Raw α β} {p : (a : α) × β a} (h : p ∈ l.toList) : p.1 ∈ l := by
  rw [← mem_keys_toList, keys_eq_map, List.mem_map]
  exact ⟨p, h, rfl⟩

theorem beq_of_mem_getEntry [Ord α] [TransOrd α] {l : Raw α β} {k : α} {p} : p ∈ l.getEntry? k → k == p.1 := by
  induction l using Raw.getEntry?.induct k
  · simp [getEntry?]
  · simp_all [getEntry?]
  · simp_all [getEntry?]
  · simp_all [getEntry?]
    rintro rfl
    exact beq_iff.2 (by simpa)

attribute [local instance] ltOfOrd

theorem Ordered.pairwise [Ord α] [TransOrd α] {l : Raw α β} (h : l.Ordered) : keys (l.toList) |>.Pairwise (· < ·) := by
  induction h
  · simp
  · next s k v l r h₁ h₂ h₃ h₄ h₅ h₆ =>
    simp only [toList, keys_append, keys_cons, List.pairwise_append, List.pairwise_cons,
      List.mem_cons, forall_eq_or_imp]
    refine ⟨h₅, ⟨by simpa [mem_keys_toList], h₆⟩, fun a ha => ⟨h₃ a (mem_keys_toList.1 ha), fun b hb => ?_⟩⟩
    exact lt_trans (h₃ a (mem_keys_toList.1 ha)) (h₄ b (mem_keys_toList.1 hb))

theorem Ordered.pairwise' [Ord α] [TransOrd α] {l : Raw α β} (h : l.Ordered) : l.toList.Pairwise (·.1 < ·.1) := by
  have := h.pairwise
  rwa [keys_eq_map, List.pairwise_map] at this

theorem Ordered.distinctKeys [Ord α] [TransOrd α] {l : Raw α β} (h : l.Ordered) : DistinctKeys l.toList :=
  ⟨h.pairwise.imp beq_eq_false_of_lt⟩

theorem perm_rotate {l l' : List α} {x : α} : (l ++ x :: l').Perm (l' ++ x :: l) := by
  -- Surely there is a tactic that can solve this?!
  rw [← List.singleton_append]
  refine List.perm_append_comm.trans ?_
  refine (List.perm_append_right_iff _).2 List.perm_append_comm |>.trans ?_
  rw [List.append_assoc, List.singleton_append]

theorem Ordered.containsKey_left [Ord α] [TransOrd α] {s ky y l r}
    (h : (Raw.inner s ky y l r : Raw α β).Ordered) : containsKey ky l.toList = false := by
  have h := h.distinctKeys
  rw [toList_inner] at h
  exact (distinctKeys_of_sublist (List.sublist_append_right _ _) (h.perm perm_rotate)).containsKey_eq_false

theorem Ordered.containsKey_right [Ord α] [TransOrd α] {s ky y l r}
    (h : (Raw.inner s ky y l r : Raw α β).Ordered) : containsKey ky r.toList = false := by
  have h := h.distinctKeys
  rw [toList_inner] at h
  exact (distinctKeys_of_sublist (List.sublist_append_right _ _) h).containsKey_eq_false

theorem Ordered.containsKey_right_of_isLE [Ord α] [TransOrd α] {k : α} {s ky y l r} (h₁ : compare k ky |>.isLE)
    (h : (Raw.inner s ky y l r : Raw α β).Ordered) : containsKey k r.toList = false := by
  simp only [containsKey_eq_false_iff_forall_mem_keys, mem_keys_toList]
  exact fun a ha => beq_eq_false_of_lt (lt_of_le_of_lt h₁ <| h.compare_right ha)

theorem Ordered.containsKey_left_of_isLE [Ord α] [TransOrd α] {k : α} {s ky y l r} (h₁ : compare ky k |>.isLE)
    (h : (Raw.inner s ky y l r : Raw α β).Ordered) : containsKey k l.toList = false := by
  simp only [containsKey_eq_false_iff_forall_mem_keys, mem_keys_toList]
  exact fun a ha => BEq.symm_false <| beq_eq_false_of_lt (lt_of_lt_of_le (h.compare_left ha) h₁)

-- theorem head_toList? [Ord α] [TransOrd α] (l : Raw α β) (k : α)

theorem mem_keys_of_mem {l : List ((a : α) × β a)} {p : (a : α) × β a} (h : p ∈ l) : p.1 ∈ keys l := by
  rw [keys_eq_map, List.mem_map]
  exact ⟨_, ⟨h, rfl⟩⟩

theorem Ordered.isLE_compare_head? [Ord α] [TransOrd α] (l : Raw α β) (k : α) (hk : k ∈ l) (hO : l.Ordered) :
    ∀ p ∈ l.toList.head?, compare p.1 k |>.isLE := by
  induction l with
  | leaf => simp
  | inner _ ky y l r ih₁ _ =>
    rintro p hp
    simp only [toList_inner, List.head?_append, List.head?_cons, Option.mem_def, Option.or_eq_some,
      List.head?_eq_none_iff, Option.some.injEq] at hp
    simp only [mem_inner_iff] at hk
    rcases hp with (hp|⟨hp, rfl⟩) <;> rcases hk with (hk|rfl|hk)
    · exact ih₁ hk hO.left _ hp
    · exact Ordering.isLE_of_eq_lt (hO.compare_left (mem_keys_toList.1 (mem_keys_of_mem (List.mem_of_mem_head? hp))))
    · exact Ordering.isLE_of_eq_lt (lt_trans (hO.compare_left (mem_keys_toList.1 (mem_keys_of_mem (List.mem_of_mem_head? hp)))) (hO.compare_right hk))
    · simp [← mem_keys_toList, hp] at hk
    · exact Ordering.isLE_of_eq_eq (beq_iff.1 BEq.refl)
    · exact Ordering.isLE_of_eq_lt (hO.compare_right hk)

theorem exists_cell_of_update [Ord α] (l : Raw α β) (k : α)
    (f : Option ((a : α) × β a) → Option ((a : α) × β a)) : ∃ (l' : List ((a : α) × β a)),
    l.toList.Perm ((l.getEntry? k).toList ++ l') ∧
    (l.updateAtKey k f).toList.Perm ((f (l.getEntry? k)).toList ++ l') ∧
    (∀ [TransOrd α], l.Ordered → containsKey k l' = false) := by
  induction l using updateAtKey.induct k f
  · simp_all [getEntry?, updateAtKey]
  · simp_all [getEntry?, updateAtKey]
  · rename_i sz ky y l r hcmp ih
    rcases ih with ⟨l', hl'₁, hl'₂, hl'₃⟩
    simp only [toList_inner, getEntry?, hcmp, updateAtKey]
    refine ⟨l' ++ ⟨ky, y⟩ :: r.toList, ?_, ?_, ?_⟩
    · simpa only [← List.append_assoc, List.perm_append_right_iff]
    · simpa only [← List.append_assoc, List.perm_append_right_iff]
    · intro _ hO
      simp only [containsKey_append, containsKey_cons, Bool.or_eq_false_iff]
      refine ⟨hl'₃ hO.left, BEq.symm_false (beq_eq_false_of_lt hcmp), ?_⟩
      apply hO.containsKey_right_of_isLE
      exact Ordering.isLE_of_eq_lt hcmp
  · rename_i sz ky y l r hcmp hf
    simp [getEntry?, hcmp, updateAtKey, hf]
    refine ⟨l.toList ++ r.toList, by simp, by simp, ?_⟩
    intro _ hO
    simp only [containsKey_append, Bool.or_eq_false_iff]
    have hcmp := beq_symm (beq_iff.2 hcmp)
    refine ⟨hO.containsKey_left_of_isLE (le_iff.1 (le_of_beq hcmp)),
      hO.containsKey_right_of_isLE (le_iff.1 (le_of_beq (beq_symm hcmp)))⟩
  · rename_i sz ky y l r hcmp k' v' hf
    simp [getEntry?, hcmp, updateAtKey, hf]
    refine ⟨l.toList ++ r.toList, by simp, by simp, ?_⟩
    intro _ hO
    simp only [containsKey_append, Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · apply hO.containsKey_left_of_isLE
      exact le_of_beq (BEq.symm (beq_iff.2 hcmp))
    · apply hO.containsKey_right_of_isLE
      exact le_of_beq (beq_iff.2 hcmp)
  · rename_i sz ky y l r hcmp ih
    rcases ih with ⟨l', hl'₁, hl'₂, hl'₃⟩
    simp only [toList_inner, getEntry?, hcmp, updateAtKey]
    refine ⟨l' ++ ⟨ky, y⟩ :: l.toList, ?_, ?_, ?_⟩
    · simp only [← List.append_assoc]
      exact perm_rotate.trans ((List.perm_append_right_iff _).2 hl'₁)
    · simp only [← List.append_assoc]
      exact perm_rotate.trans ((List.perm_append_right_iff _).2 hl'₂)
    · intro _ hO
      simp only [containsKey_append, containsKey_cons, Bool.or_eq_false_iff]
      refine ⟨hl'₃ hO.right, beq_eq_false_of_lt (lt_iff'.2 hcmp), ?_⟩
      apply hO.containsKey_left_of_isLE
      exact Ordering.isLE_of_eq_lt (by rwa [compare_eq_gt_iff] at hcmp)

theorem mem_updateAtKey [Ord α] [TransOrd α] {l : Raw α β} {k k₀ : α} {f}
    (hf : ∀ (l : Option ((a : α) × β a)), (∀ p ∈ l, p.1 == k) → ∀ p ∈ f l, p.1 == k) :
    k₀ ∈ l.updateAtKey k f → k₀ ∈ l ∨ k₀ == k := by
  induction l using Raw.updateAtKey.induct k f
  · simp_all [Raw.updateAtKey]
  · rename_i k' v' hfn
    simp only [updateAtKey, hfn, mem_inner_iff, not_mem_leaf, or_false, false_or]
    rintro rfl
    exact hf none (by simp) ⟨k₀, v'⟩ (by simp [hfn])
  · rename_i sz ky y l r hcmp ih
    simp only [updateAtKey, hcmp, mem_inner_iff]
    rintro (h|rfl|h)
    · exact (ih h).elim (Or.inl ∘ Or.inl) Or.inr
    · simp
    · simp_all
  · rename_i sz k' v' l r hcmp hf
    simp only [updateAtKey, hcmp, hf, mem_glueRaw, mem_inner_iff]
    rintro (h|h) <;> simp_all
  · rename_i sz ky y l r hcmp k' v' hfs
    simp only [updateAtKey, hcmp, hfs, mem_inner_iff]
    rintro (h|rfl|h)
    · simp_all
    · exact Or.inr <| hf (some ⟨ky, y⟩) (by simpa using BEq.symm (beq_iff.2 hcmp)) ⟨k₀, v'⟩ (by simp [hfs])
    · simp_all
  · rename_i sz ky y l r hcmp ih
    simp only [updateAtKey, hcmp, mem_inner_iff]
    rintro (h|rfl|h)
    · simp_all
    · simp
    · exact (ih h).elim (Or.inl ∘ Or.inr ∘ Or.inr) Or.inr

theorem Ordered.updateAtKey [Ord α] [TransOrd α] {l : Raw α β} {k : α}
    {f : Option ((a : α) × β a) → Option ((a : α) × β a)}
    (hf : ∀ (l : Option ((a : α) × β a)), (∀ p ∈ l, p.1 == k) → ∀ p ∈ f l, p.1 == k)
    (hO : l.Ordered) : (l.updateAtKey k f).Ordered := by
  induction l using Raw.updateAtKey.induct k f
  · simp_all [Raw.updateAtKey]
  · simp_all [Raw.updateAtKey]
  · rename_i sz ky y l r hcmp ih
    simp only [Raw.updateAtKey, hcmp]
    refine Ordered.inner (ih hO.left) hO.right ?_ ?_
    · intro k' hk'
      rcases mem_updateAtKey hf hk' with (hk'|hk')
      · exact hO.compare_left hk'
      · exact lt_of_beq_of_lt hk' hcmp
    · exact fun k' hk' => hO.compare_right hk'
  · rename_i sz ky y l lr hcmp hf
    simp only [Raw.updateAtKey, hcmp, hf]
    refine ordered_glueRaw hO.left hO.right ?_
    intro k₁ k₂ hk₁ hk₂
    exact lt_iff.1 (lt_trans (lt_iff.2 (hO.compare_left hk₁)) (lt_iff.2 (hO.compare_right hk₂)))
  · rename_i sz ky y l r hcmp k' v' hfs
    simp only [Raw.updateAtKey, hcmp, hfs]
    refine Ordered.inner hO.left hO.right ?_ ?_
    · intro k₁ hk₁
      have hc₁ := hO.compare_left hk₁
      have hc₂ := hf (some ⟨ky, y⟩) (by simpa using BEq.symm (beq_iff.2 hcmp)) ⟨k', v'⟩ (by simp [hfs])
      exact lt_of_lt_of_beq hc₁ (BEq.trans (BEq.symm (beq_iff.2 hcmp)) (BEq.symm hc₂))
    · intro k₁ hk₁
      have hc₁ := hO.compare_right hk₁
      have hc₂ := hf (some ⟨ky, y⟩) (by simpa using BEq.symm (beq_iff.2 hcmp)) ⟨k', v'⟩ (by simp [hfs])
      exact lt_of_beq_of_lt (BEq.trans hc₂ (beq_iff.2 hcmp)) hc₁
  · rename_i sz ky y l r hcmp ih
    simp only [Raw.updateAtKey, hcmp]
    refine Ordered.inner hO.left (ih hO.right) ?_ ?_
    · exact fun k' hk' => hO.compare_left hk'
    · intro k' hk'
      rcases mem_updateAtKey hf hk' with (hk'|hk')
      · exact hO.compare_right hk'
      · exact lt_of_lt_of_beq (compare_eq_gt_iff.1 hcmp) (BEq.symm hk')

theorem Ordered.insertₘ [Ord α] [TransOrd α] {l : Raw α β} {k : α} {v : β k}
    (hl : l.Ordered) : (l.insertₘ k v).Ordered :=
  Ordered.updateAtKey (by simp) hl

theorem exists_cell [Ord α] (l : Raw α β) (k : α) : ∃ (l' : List ((a : α) × β a)),
    l.toList.Perm ((l.getEntry? k).toList ++ l') ∧
    (∀ [TransOrd α], l.Ordered → containsKey k l' = false) := by
  obtain ⟨l', h₁, -, h₂⟩ := exists_cell_of_update l k id
  exact ⟨l', h₁, h₂⟩

theorem toList_insert [Ord α] [TransOrd α] (l : Raw α β) (k : α) (v : β k) (h : l.Ordered) (h' : l.Balanced) :
    List.Perm (toList (Raw.insert k v ⟨l, h'⟩)) (insertEntry k v l.toList) := by
  rw [toList_insert_eq_toList_insertWithoutRebalancing,
      toList_insertWithoutRebalancing_eq_toList_insertₘ]

  have hfg : ∀ (l : Option ((a : α) × β a)), (∀ p ∈ l, p.1 == k) → (some ⟨k, v⟩).toList = insertEntry k v l.toList := by
    rintro (_|p)
    · simp
    · intro h'
      simp only [Option.toList_some]
      rw [insertEntry_of_containsKey (containsKey_cons_of_beq (h' p rfl)), replaceEntry_cons_of_true (h' p rfl)]

  obtain ⟨l', h₁, h₂, h₃⟩ := exists_cell_of_update l k (fun _ => some ⟨k, v⟩)
  refine h₂.trans (List.Perm.trans ?_ (insertEntry_of_perm h.distinctKeys h₁).symm)
  rw [insertEntry_append_of_not_contains_right (h₃ h), hfg]
  exact fun p hp => BEq.symm (beq_of_mem_getEntry hp)

theorem apply_explore [Ord α] [TransOrd α] {γ : Type w} {l : Raw α β}

    (P : Raw α β → Prop)
    (hPl : ∀ {sz ky y l r}, P (Raw.inner sz ky y l r : Raw α β) → P l)
    (hPr : ∀ {sz ky y l r}, P (Raw.inner sz ky y l r : Raw α β) → P r)
    (hP : P l)

    (hl : l.Ordered) {k : α} {init : γ}

    (f : γ → ExplorationStep α β → γ)
    (g : List ((a : α) × β a) → Option ((a : α) × β a) → List ((a : α) × β a) → γ)
    (h : List ((a : α) × β a) → γ)

    (hfg₁ : ∀ l₁ l₂ ky y r, P r → f (g l₁ none l₂) (.lt ky y r) = g l₁ none (⟨ky, y⟩ :: r.toList ++ l₂))
    (hfg₂ : ∀ l₁ l₂ l ky y r, P l → P r → f (g l₁ none l₂) (.eq l ky y r) = g (l₁ ++ l.toList) (some ⟨ky, y⟩) (r.toList ++ l₂))
    (hfg₃ : ∀ l₁ l₂ l ky y, P l → f (g l₁ none l₂) (.gt l ky y) = g (l₁ ++ l.toList ++ [⟨ky, y⟩]) none l₂)

    (hg₀ : g [] none [] = init)

    (hgh : ∀ l₁ o l₂, (∀ p ∈ l₁, compare p.1 k = .lt) →
      (∀ p ∈ o, compare p.1 k = .eq) →
      (∀ p ∈ l₂, compare k p.1 = .lt) →
      (l₁.Pairwise (fun p q => compare p.1 q.1 = .lt)) →
      (l₂.Pairwise (fun p q => compare p.1 q.1 = .lt)) →
      g l₁ o l₂ = h (l₁ ++ o.toList ++ l₂))

    :
    explore k init f l = h (l.toList) := by
  have step₁ : explore k init f l = g (l.toList.filter (·.1 < k)) (l.toList.find? (·.1 == k)) (l.toList.filter (k < ·.1)) := by
    suffices ∀ (l₁ l₂ : List ((a : α) × β a)) (hl₁ : ∀ (p) (hp : p ∈ l₁) (k' : α), k' ∈ l → p.1 < k') (hl₂ : ∀ (p) (hp : p ∈ l₂) (k' : α), k' ∈ l → k' < p.1),
        explore k (g l₁ none l₂) f l = g (l₁ ++ l.toList.filter (·.1 < k)) (l.toList.find? (·.1 == k)) (l.toList.filter (k < ·.1) ++ l₂) by
      simpa [hg₀] using this [] [] (by simp) (by simp)
    intro l₁ l₂ hl₁ hl₂
    induction l generalizing l₁ l₂ with
    | leaf => simp [explore]
    | inner sz k' v' l r ih₁ ih₂ =>
      simp only [explore, toList_inner, List.filter_append, List.find?_append]
      split <;> rename_i hcmp
      · rw [hfg₁ _ _ _ _ _ (hPr hP), ih₁ (hPl hP) hl.left]
        · have hp' (p) (hp : p ∈ r.toList) : k < p.1 := lt_trans hcmp (hl.compare_right (mem_of_mem_toList hp))
          congr 1
          · simp only [List.append_cancel_left_eq, List.self_eq_append_right,
              List.filter_eq_nil_iff, List.mem_cons, decide_eq_true_eq, forall_eq_or_imp]
            exact ⟨not_lt_of_lt hcmp, fun p hp => not_lt_of_lt (hp' _ hp)⟩
          · suffices List.find? (·.1 == k) (⟨k', v'⟩ :: r.toList) = none by simp [this]
            simp only [List.find?_eq_none, List.mem_cons, Bool.not_eq_true, forall_eq_or_imp]
            exact ⟨BEq.symm_false (beq_eq_false_of_lt hcmp), (fun p hp => BEq.symm_false (beq_eq_false_of_lt (hp' _ hp)))⟩
          · simp only [List.cons_append, List.append_assoc, List.append_cancel_left_eq]
            rw [List.filter_eq_self.2]
            · simp only [List.cons_append]
            · simp only [List.mem_cons, decide_eq_true_eq, forall_eq_or_imp]
              exact ⟨hcmp, hp'⟩
        · exact fun p hp k' hk' => hl₁ p hp k' (mem_inner_iff.2 (Or.inl hk'))
        · intro p hp k'' hk''
          rcases List.mem_append.1 hp with hp|hp
          · rcases List.mem_cons.1 hp with rfl|hp
            · exact hl.compare_left hk''
            · exact lt_trans (hl.compare_left hk'') (hl.compare_right (mem_of_mem_toList hp))
          · exact hl₂ p hp k'' (mem_inner_iff.2 (Or.inl hk''))
      · rw [hfg₂ _ _ _ _ _ _ (hPl hP) (hPr hP)]
        have hpr (p) (hp : p ∈ r.toList) : k < p.1 := lt_of_beq_of_lt (beq_iff.2 hcmp) (hl.compare_right (mem_of_mem_toList hp))
        have hpl (p) (hp : p ∈ l.toList) : p.1 < k := lt_of_lt_of_beq (hl.compare_left (mem_of_mem_toList hp)) (BEq.symm (beq_iff.2 hcmp))
        congr 1
        · rw [List.append_cancel_left_eq, List.filter_eq_self.2, List.filter_eq_nil_iff.2, List.append_nil]
          · simp only [List.mem_cons, decide_eq_true_eq, forall_eq_or_imp]
            exact ⟨not_lt_of_beq (BEq.symm (beq_iff.2 hcmp)), fun p hp => not_lt_of_lt (hpr _ hp)⟩
          · simpa using hpl
        · rw [List.find?_eq_none.2, Option.none_or, List.find?_cons_of_pos]
          · exact BEq.symm (beq_iff.2 hcmp)
          · simp only [Bool.not_eq_true]
            exact fun p hp => beq_eq_false_of_lt (hpl _ hp)
        · rw [List.filter_eq_nil_iff.2, List.nil_append, List.filter_cons_of_neg, List.filter_eq_self.2]
          · simpa using hpr
          · simp only [decide_eq_true_eq]
            exact not_lt_of_beq (beq_iff.2 hcmp)
          · simp only [decide_eq_true_eq]
            exact fun p hp => not_lt_of_lt (hpl _ hp)
      · rw [← lt_iff'] at hcmp
        rw [hfg₃ _ _ _ _ _ (hPl hP), ih₂ (hPr hP) hl.right]
        have hp' (p) (hp : p ∈ l.toList) : p.1 < k := lt_trans (hl.compare_left (mem_of_mem_toList hp)) hcmp
        · congr 1
          · simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq]
            rw [Eq.comm, List.filter_eq_self.2, List.filter_cons_of_pos] <;> simpa
          · rw [Eq.comm, List.find?_eq_none.2, Option.none_or, List.find?_cons_of_neg]
            · simp only [Bool.not_eq_true]
              exact beq_eq_false_of_lt hcmp
            · simp only [Bool.not_eq_true]
              exact fun p hp => beq_eq_false_of_lt (hp' _ hp)
          · rw [Eq.comm, List.filter_eq_nil_iff.2, List.nil_append, List.filter_cons_of_neg]
            · simpa using not_lt_of_lt hcmp
            · simp only [decide_eq_true_eq]
              exact fun p hp => not_lt_of_lt (hp' _ hp)
        · simp only [List.append_assoc, List.mem_append, List.mem_singleton]
          rintro p (hp|hp|rfl) k'' hk''
          · exact hl₁ p hp k'' (mem_inner_iff.2 (Or.inr (Or.inr hk'')))
          · exact lt_trans (hl.compare_left (mem_of_mem_toList hp)) (hl.compare_right hk'')
          · exact hl.compare_right hk''
        · exact fun p hp k'' hk'' => hl₂ p hp k'' (mem_inner_iff.2 (Or.inr (Or.inr hk'')))

  rw [step₁, hgh, List.append_assoc, ← eq_append]
  · exact hl.pairwise'
  · simpa using fun _ _ => id
  · simpa [List.find?_eq_some] using fun _ h _ _ _ _ => beq_iff.1 h
  · simpa using fun _ _ => id
  · exact hl.pairwise'.sublist (List.filter_sublist _)
  · exact hl.pairwise'.sublist (List.filter_sublist _)

theorem apply_lowerBound?ₘ [Ord α] [TransOrd α] {l : Raw α β} (hl : l.Ordered) {k : α} :
    l.lowerBound?ₘ k = Std.DHashMap.Internal.List.lowerBound? l.toList k := by
  rw [lowerBound?ₘ]
  let f : Option ((a : α) × β a) → ExplorationStep α β → Option ((a : α) × β a) := fun sofar step =>
    match step with
    | .lt ky y _ => some ⟨ky, y⟩
    | .eq _ ky y _ => some ⟨ky, y⟩
    | .gt _ _ _ => sofar
  let g : List ((a : α) × β a) → Option ((a : α) × β a) → List ((a : α) × β a) → Option ((a : α) × β a) :=
    fun _ o l₂ => o.or l₂.head?
  let h : List ((a : α) × β a) → Option ((a : α) × β a) := (Std.DHashMap.Internal.List.lowerBound? · k)

  have hfg₁ : ∀ l₁ l₂ ky y r, True → f (g l₁ none l₂) (.lt ky y r) = g l₁ none (⟨ky, y⟩ :: r.toList ++ l₂) := by
    simp [f, g]
  have hfg₂ : ∀ l₁ l₂ l ky y r, True → True → f (g l₁ none l₂) (.eq l ky y r) = g (l₁ ++ l.toList) (some ⟨ky, y⟩) (r.toList ++ l₂) := by
    simp [f, g]
  have hfg₃ : ∀ l₁ l₂ l ky y, True → f (g l₁ none l₂) (.gt l ky y) = g (l₁ ++ l.toList ++ [⟨ky, y⟩]) none l₂ := by
    simp [f, g]

  have hg₀ : g [] none [] = none := by simp [g]

  have hgh : ∀ l₁ o l₂, (∀ p ∈ l₁, compare p.1 k = .lt) →
      (∀ p ∈ o, compare p.1 k = .eq) →
      (∀ p ∈ l₂, compare k p.1 = .lt) →
      (l₁.Pairwise (fun p q => compare p.1 q.1 = .lt)) →
      (l₂.Pairwise (fun p q => compare p.1 q.1 = .lt)) →
      g l₁ o l₂ = h (l₁ ++ o.toList ++ l₂) := by
    intro l₁ o l₂ hl₁ ho hl₂ hl₁' hl₂'
    simp only [List.append_assoc, g, h]
    cases o with
    | none =>
      simp only [Option.none_or, Option.toList_none, List.nil_append]
      rw [lowerBound?_append_of_forall_mem_left hl₁, lowerBound?_eq_head? (le_of_lt <| hl₂ · ·) hl₂']
    | some p =>
      simp only [Option.or_some, Option.toList_some, List.singleton_append]
      rw [lowerBound?_append_of_forall_mem_left hl₁]
      simp only [Option.mem_def, Option.some.injEq, forall_eq'] at ho
      rw [lowerBound?_cons_eq_self]
      · exact le_of_beq (BEq.symm (beq_iff.2 ho))
      · exact fun q hq => Or.inr (le_of_lt (lt_of_beq_of_lt (beq_iff.2 ho) (hl₂ _ hq)))

  exact apply_explore (fun _ => True) (by simp) (by simp) (by simp) hl f g h hfg₁ hfg₂ hfg₃ hg₀ hgh

theorem apply_insertionPoint [Ord α] [TransOrd α] {l : Raw α β} (hl : l.Ordered) (hl' : l.Sized) {k : α} :
    l.insertionPoint k = rank k l.toList := by
  rw [insertionPoint_eq_insertionPointₘ, insertionPointₘ]
  let f : Nat → ExplorationStep α β → Nat := fun sofar step =>
    match step with
    | .lt _ _ _ => sofar
    | .eq l _ _ _ => sofar + l.size
    | .gt l _ _ => sofar + 1 + l.size
  let g : List ((a : α) × β a) → Option ((a : α) × β a) → List ((a : α) × β a) → Nat :=
    fun l₁ _ _ => l₁.length
  let h : List ((a : α) × β a) → Nat := rank k

  have hfg₁ : ∀ l₁ l₂ ky y r, r.Sized → f (g l₁ none l₂) (.lt ky y r) = g l₁ none (⟨ky, y⟩ :: r.toList ++ l₂) := by
    simp [f, g]
  have hfg₂ : ∀ l₁ l₂ l ky y r, l.Sized → r.Sized → f (g l₁ none l₂) (.eq l ky y r) = g (l₁ ++ l.toList) (some ⟨ky, y⟩) (r.toList ++ l₂) := by
    intro l₁ l₂ l ky y r hl hr
    simp [f, g, hl.length_toList]
  have hfg₃ : ∀ l₁ l₂ l ky y, l.Sized → f (g l₁ none l₂) (.gt l ky y) = g (l₁ ++ l.toList ++ [⟨ky, y⟩]) none l₂ := by
    intro l₁ l₂ l ky y hl
    simp [f, g, hl.length_toList]
    ac_rfl

  have hg₀ : g [] none [] = 0 := by simp [g]

  have hgh : ∀ l₁ o l₂, (∀ p ∈ l₁, compare p.1 k = .lt) →
      (∀ p ∈ o, compare p.1 k = .eq) →
      (∀ p ∈ l₂, compare k p.1 = .lt) →
      (l₁.Pairwise (fun p q => compare p.1 q.1 = .lt)) →
      (l₂.Pairwise (fun p q => compare p.1 q.1 = .lt)) →
      g l₁ o l₂ = h (l₁ ++ o.toList ++ l₂) := by
    intro l₁ o l₂ hl₁ ho hl₂ hl₁' hl₂'
    simp only [List.append_assoc, g, h]
    rw [rank_append_eq_left, rank_eq_length hl₁]
    simp only [List.mem_append, Option.mem_toList, Option.mem_def]
    rintro p (rfl|hp)
    · exact le_of_beq (BEq.symm (beq_iff.2 (by simpa using ho)))
    · exact le_of_lt (hl₂ _ hp)

  exact apply_explore Sized Sized.left Sized.right hl' hl f g h hfg₁ hfg₂ hfg₃ hg₀ hgh

end Raw

end DOrderedTree

end Std
