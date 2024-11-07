/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Impl.Attr
import Lean.Elab.Tactic

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
Asaaa
-/

set_option autoImplicit false
set_option linter.all true

universe u v

variable {α : Type u} {β : α → Type v}

namespace Std.DOrderedTree.Internal

/-- (Implementation detail) The actual inductive type for the size-balanced tree data structure. -/
inductive Impl (α : Type u) (β : α → Type v) where
  /-- (Implementation detail) -/
  | inner (size : Nat) (k : α) (v : β k) (l r : Impl α β)
  /-- (Implementation detail) -/
  | leaf
  deriving Inhabited

/-- The "delta" parameter of the size-bounded tree. Controls how imbalanced the tree can be. -/
@[inline, tree_tac]
def delta : Nat := 3

/-- The "ratio" parameter of the size-bounded tree. Controls how aggressive the rebalancing
operations are. -/
@[inline, tree_tac]
def ratio : Nat := 2

namespace Impl

/-- The size information stored in the tree. -/
@[inline]
def size : Impl α β → Nat
  | inner sz _ _ _ _ => sz
  | leaf => 0

@[tree_tac] theorem size_leaf : (Impl.leaf : Impl α β).size = 0 := rfl
@[tree_tac] theorem size_inner {sz k v l r} : (Impl.inner sz k v l r : Impl α β).size = sz := rfl

/-- Predicate for local balance at a node of the tree. We don't provide API for this, preferring
instead to use automation to dispatch goals about balance. -/
@[tree_tac]
def BalancedAtRoot (left right : Nat) : Prop :=
  left + right ≤ 1 ∨ (left ≤ delta * right ∧ right ≤ delta * left)

/-- Predicate that states that the stored size information in a tree is correct and that it is
balanced. -/
inductive Balanced : Impl α β → Prop where
  /-- Leaf is balanced. -/
  | leaf : Balanced leaf
  /-- Inner node is balanced if it is locally balanced, both children are balanced and size
  information is correct. -/
  | inner {sz k v l r} : Balanced l → Balanced r →
      BalancedAtRoot l.size r.size → sz = l.size + 1 + r.size → Balanced (inner sz k v l r)

attribute [tree_tac] Balanced.leaf

@[tree_tac]
theorem balanced_inner_iff {sz k v l r} : Balanced (Impl.inner sz k v l r : Impl α β) ↔
    Balanced l ∧ Balanced r ∧ BalancedAtRoot l.size r.size ∧ sz = l.size + 1 + r.size :=
  ⟨by rintro (_|⟨h₁, h₂, h₃, h₄⟩); exact ⟨h₁, h₂, h₃, h₄⟩,
   fun ⟨h₁, h₂, h₃, h₄⟩ => .inner h₁ h₂ h₃ h₄⟩

/-!
## Balancing operations
-/

/-- Precondition for `balanceL`: at most one element was added to left subtree. -/
@[tree_tac]
abbrev BalanceLPrecond (left right : Nat) :=
  BalancedAtRoot left right ∨ (1 ≤ left ∧ BalancedAtRoot (left - 1) right)

section

open Lean Meta Elab Tactic

-- TODO: Can't use `elab` in Std
/-- (Implementation detail) -/
elab "split_and" : tactic => liftMetaTactic fun mvarId => do
  let hyps ← getPropHyps
  for hyp in hyps do
    let t ← instantiateMVars (← hyp.getType)
    if let .app (.app (.const `And _) _) _ := t then
      return (← runTactic mvarId (← `(tactic| cases $(Lean.mkIdent (← hyp.getUserName)):term))).1
  throwError "no matching hypothesis found"

/-- (Implementation detail) -/
macro "tree_tac" : tactic => `(tactic|(
  repeat' split
  all_goals
    simp only [tree_tac] at *
    repeat' split_and
    repeat' apply And.intro
  all_goals
    try assumption
    try contradiction
  all_goals
    omega
  ))

end

/-!
### `balanceL` variants
-/

/-- Rebalances a tree after at most one element was added to the left subtree. Uses balancing
information to show that some cases are impossible. -/
@[inline]
def balanceL (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLPrecond l.size r.size) : Impl α β :=
  match r with
  | leaf => match l with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v l .leaf
    | inner _ lk lv .leaf (.inner _ lrk lrv _ _) =>
        .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf) (.inner 1 k v .leaf .leaf)
    | inner _ lk lv ll@(.inner _ _ _ _ _) .leaf =>
        .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
    | inner ls lk lv (.inner lls _ _ _ _) (.inner lrs _ _ _ _) => False.elim (by tree_tac)
  | inner rs _ _ _ _ => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | inner ls lk lv ll lr =>
        if hlsd : ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | leaf, _ => False.elim (by tree_tac)
          | _, leaf => False.elim (by tree_tac)
        else .inner (1 + ls + rs) k v l r

@[tree_tac]
theorem size_balanceL {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceL k v l r hrb hlb hlr).size = l.size + 1 + r.size := by
  simp only [balanceL.eq_def]; tree_tac

@[tree_tac]
theorem balanced_balanceL {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceL k v l r hrb hlb hlr).Balanced := by
  simp only [balanceL.eq_def]; tree_tac

/-- Slower version of `balanceL` with weaker balancing assumptions that hold after erasing from
the right side of the tree. -/
@[inline] def balanceLErase (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalancedAtRoot l.size (r.size + 1) ∨ BalancedAtRoot l.size r.size) : Impl α β :=
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
        else .inner (1 + ls) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
          (.inner (1 + lrr.size) k v lrr .leaf)
  | (inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | inner ls lk lv ll lr =>
        if hlsd : ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | leaf, _ => False.elim (by tree_tac)
          | _, leaf => False.elim (by tree_tac)
        else .inner (1 + ls + rs) k v l r

@[tree_tac]
theorem size_balanceLErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceLErase k v l r hrb hlb hlr).size = l.size + 1 + r.size := by
  simp only [balanceLErase.eq_def]; tree_tac

@[tree_tac]
theorem balanced_balanceLErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceLErase k v l r hrb hlb hlr).Balanced := by
  simp only [balanceLErase.eq_def]; tree_tac

/-- Slow version of `balanceL` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balanceL` or `balanceL` are satisfied
(otherwise panics). -/
@[inline] def balanceLSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
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
        else .inner (1 + ls) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
          (.inner (1 + lrr.size) k v lrr .leaf)
  | (inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | inner ls lk lv ll lr =>
        if ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | leaf, _ => panic! "balanceLSlow input was not balanced"
          | _, leaf => panic! "balanceLSlow input was not balanced"
        else .inner (1 + ls + rs) k v l r

/-!
### `balanceR` variants
-/

/-- Rebalances a tree after at most one element was added to the right subtree. Uses balancing
information to show that some cases are impossible. -/
@[inline]
def balanceR (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLPrecond r.size l.size) : Impl α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        False.elim (by tree_tac)
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if hrsd : rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then
                .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else
                .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                  (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | leaf, _ => False.elim (by tree_tac)
          | _, leaf => False.elim (by tree_tac)
        else .inner (1 + ls + rs) k v l r

@[tree_tac]
theorem size_balanceR {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceR k v l r hrb hlb hlr).size = l.size + 1 + r.size := by
  simp only [balanceR.eq_def]; tree_tac

@[tree_tac]
theorem balanced_balanceR {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceR k v l r hrb hlb hlr).Balanced := by
  simp only [balanceR.eq_def]; tree_tac

/-- Slower version of `balanceR` with weaker balancing assumptions that hold after erasing from
the left side of the tree. -/
@[inline]
def balanceRErase (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalancedAtRoot (1 + l.size) r.size ∨ BalancedAtRoot l.size r.size) : Impl α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        if rls < ratio * rrs then .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
        else .inner (1 + rs) rlk rlv
          (.inner (1 + rll.size) k v .leaf rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if hrsd : rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then
                .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else
                .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                  (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | leaf, _ => False.elim (by tree_tac)
          | _, leaf => False.elim (by tree_tac)
        else .inner (1 + ls + rs) k v l r

@[tree_tac]
theorem size_balanceRErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceRErase k v l r hrb hlb hlr).size = l.size + 1 + r.size := by
  simp only [balanceRErase.eq_def]; tree_tac

@[tree_tac]
theorem balanced_balanceRErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balanceRErase k v l r hrb hlb hlr).Balanced := by
  simp only [balanceRErase.eq_def]; tree_tac

/-- Slow version of `balanceR` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balanceR` or `balanceRErase` are satisfied
(otherwise panics). -/
@[inline]
def balanceRSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        if rls < ratio * rrs then .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
        else .inner (1 + rs) rlk rlv
          (.inner (1 + rll.size) k v .leaf rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then
                .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else
                .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                  (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | leaf, _ => panic! "balanceRSlow input was not balanced"
          | _, leaf => panic! "balanceRSlow input was not balanced"
        else .inner (1 + ls + rs) k v l r

/-!
## `minView` and `maxView`
-/

variable (α β) in
/-- A tuple of a key-value pair and a tree. -/
structure RawView where
  /-- The key. -/
  k : α
  /-- The value. -/
  v : β k
  /-- The tree. -/
  tree : Impl α β

variable (α β) in
/-- A tuple of a key-value pair and a balanced tree of size `size`. -/
structure View (size : Nat) where
  /-- The tuple. -/
  raw : RawView α β
  /-- The tree is balanced. -/
  balanced_tree : raw.tree.Balanced
  /-- The tree has size `size`. -/
  size_tree : raw.tree.size = size

attribute [tree_tac] View.balanced_tree View.size_tree

/-- Returns the tree `l ++ ⟨k, v⟩ ++ r`, with the smallest element chopped off. -/
def minView (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hlr : BalancedAtRoot l.size r.size) : View α β (l.size + r.size) :=
  match l with
  | leaf => ⟨⟨k, v, r⟩, hr, by tree_tac⟩
  | inner _ k' v' l' r' =>
      let d := minView k' v' l' r' (by tree_tac) (by tree_tac) (by tree_tac)
      ⟨⟨d.raw.k, d.raw.v, balanceRErase k v d.raw.tree r (by tree_tac) (by tree_tac)
            (by simp only [tree_tac] at hl; tree_tac)⟩,
          by tree_tac, by simp only [tree_tac] at hl; tree_tac⟩

/-- Slow version of `minView` which can be used in the absence of balance information but still
assumes the preconditions of `minView`, otherwise might panic. -/
def minViewSlow (k : α) (v : β k) (l r : Impl α β) : RawView α β :=
  match l with
  | leaf => ⟨k, v, r⟩
  | inner _ k' v' l' r' =>
      let d := minViewSlow k' v' l' r'
      ⟨d.k, d.v, balanceRSlow k v d.tree r⟩

/-- Returns the tree `l ++ ⟨k, v⟩ ++ r`, with the largest element chopped off. -/
def maxView (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hlr : BalancedAtRoot l.size r.size) : View α β (l.size + r.size) :=
  match r with
  | leaf => ⟨⟨k, v, l⟩, hl, by tree_tac⟩
  | inner _ k' v' l' r' =>
      let d := maxView k' v' l' r' (by tree_tac) (by tree_tac) (by tree_tac)
      ⟨⟨d.raw.k, d.raw.v, balanceLErase k v l d.raw.tree (by tree_tac) (by tree_tac)
            (by simp only [tree_tac] at hr; tree_tac)⟩,
          by tree_tac, by simp only [tree_tac] at hr; tree_tac⟩

/-- Slow version of `maxView` which can be used in the absence of balance information but still
assumes the preconditions of `maxView`, otherwise might panic. -/
def maxViewSlow (k : α) (v : β k) (l r : Impl α β) : RawView α β :=
  match r with
  | leaf => ⟨k, v, l⟩
  | inner _ k' v' l' r' =>
      let d := maxViewSlow k' v' l' r'
      ⟨d.k, d.v, balanceLSlow k v l d.tree⟩

/-!
## `glue`
-/

end Impl

end Std.DOrderedTree.Internal
