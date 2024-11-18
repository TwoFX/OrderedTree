/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.Classes.LawfulEqOrd
import Orderedtree.DOrderedTree.Internal.Impl.Attr
import Lean.Elab.Tactic

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option debug.byAsSorry true

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type v}

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

/-!
## Query operations
-/

/-- The size information stored in the tree. -/
@[inline]
def size : Impl α β → Nat
  | inner sz _ _ _ _ => sz
  | leaf => 0

@[tree_tac] theorem size_leaf : (Impl.leaf : Impl α β).size = 0 := rfl
@[tree_tac] theorem size_inner {sz k v l r} : (Impl.inner sz k v l r : Impl α β).size = sz := rfl

/-- Returns `true` if the given key is contained in the map. -/
def contains [Ord α] (k : α) (l : Impl α β) : Bool :=
  match l with
  | .leaf => false
  | .inner _ k' _ l r =>
    match compare k k' with
    | .lt => contains k l
    | .gt => contains k r
    | .eq => true

/-- Returns `true` if the tree is empty. -/
@[inline]
def isEmpty (l : Impl α β) : Bool :=
  match l with
  | .leaf => true
  | .inner _ _ _ _ _ => false

/-- Returns the value for the key `k`, or `none` if such a key does not exist. -/
def get? [Ord α] [LawfulEqOrd α] (k : α) (l : Impl α β) : Option (β k) :=
  match l with
  | .leaf => none
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get? k l
    | .gt => get? k r
    | .eq => some (cast (congrArg β (eq_of_compare h).symm) v')

/-- Returns the value for the key `k`. -/
def get [Ord α] [LawfulEqOrd α] (k : α) (l : Impl α β) (hlk : l.contains k = true) : β k :=
  match l with
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get k l (by simpa [contains, h] using hlk)
    | .gt => get k r (by simpa [contains, h] using hlk)
    | .eq => cast (congrArg β (eq_of_compare h).symm) v'

/-- Returns the value for the key `k`, or panics if such a key does not exist. -/
def get! [Ord α] [LawfulEqOrd α] (k : α) (l : Impl α β) [Inhabited (β k)] : β k :=
  match l with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get! k l
    | .gt => get! k r
    | .eq => cast (congrArg β (eq_of_compare h).symm) v'

/-- Returns the value for the key `k`, or `fallback` if such a key does not exist. -/
def getD [Ord α] [LawfulEqOrd α] (k : α) (l : Impl α β) (fallback : β k) : β k :=
  match l with
  | .leaf => fallback
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => getD k l fallback
    | .gt => getD k r fallback
    | .eq => cast (congrArg β (eq_of_compare h).symm) v'

namespace Const

/-- Returns the value for the key `k`, or `none` if such a key does not exist. -/
def Const.get? [Ord α] (k : α) (l : Impl α (fun _ => δ)) : Option δ :=
  match l with
  | .leaf => none
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => get? k l
    | .gt => get? k r
    | .eq => some v'

/-- Returns the value for the key `k`. -/
def get [Ord α] (k : α) (l : Impl α (fun _ => δ)) (hlk : l.contains k = true) : δ :=
  match l with
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get k l (by simpa [contains, h] using hlk)
    | .gt => get k r (by simpa [contains, h] using hlk)
    | .eq => v'

/-- Returns the value for the key `k`, or panics if such a key does not exist. -/
def get! [Ord α] (k : α) (l : Impl α (fun _ => δ)) [Inhabited δ] : δ :=
  match l with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => get! k l
    | .gt => get! k r
    | .eq => v'

/-- Returns the value for the key `k`, or `fallback` if such a key does not exist. -/
def getD [Ord α] (k : α) (l : Impl α (fun _ => δ)) (fallback : δ) : δ :=
  match l with
  | .leaf => fallback
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => getD k l fallback
    | .gt => getD k r fallback
    | .eq => v'

end Const

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

/-- Precondition for `balanceLErase`. As Breitner et al. remark, "not very educational". -/
@[tree_tac]
abbrev BalanceLErasePrecond (left right : Nat) :=
  (delta * left ≤ delta * delta * right + delta * right + right + delta ∧ right + 1 ≤ left) ∨
    BalancedAtRoot left (right + 1) ∨ BalancedAtRoot left right

section

open Lean Meta Elab Tactic

/-- (Implementation detail) -/
scoped macro "tree_tac" : tactic => `(tactic|(
  subst_eqs
  repeat' split
  all_goals
    try simp only [tree_tac] at *
  all_goals
    try simp only [tree_tac] at *
    repeat cases ‹_ ∧ _›
    repeat' apply And.intro
  all_goals
    try assumption
    try contradiction
  all_goals
    omega
  ))

/-- (Implementation detail) -/
scoped macro "✓" : term => `(term| by tree_tac)

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
    | inner ls lk lv (.inner lls _ _ _ _) (.inner lrs _ _ _ _) => False.elim ✓
  | inner rs _ _ _ _ => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | inner ls lk lv ll lr =>
        if hlsd : ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v (inner lrs lrk lrv lrl lrr) r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | leaf, _ => False.elim ✓
          | _, leaf => False.elim ✓
        else .inner (1 + ls + rs) k v (.inner ls lk lv ll lr) r

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
@[inline]
def balanceLErase (k : α) (v : β k) (l r : Impl α β) (hlb : Balanced l) (hrb : Balanced r)
    (hlr : BalanceLErasePrecond l.size r.size) : Impl α β :=
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
  | r@(inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | l@(inner ls lk lv ll lr) =>
        if hlsd : ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | leaf, _ => False.elim ✓
          | _, leaf => False.elim ✓
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
    | (inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv (.inner rls rlk rlv rll rlr) (.inner rrs _ _ _ _) =>
        False.elim ✓
  | inner ls _ _ _ _ => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | inner rs rk rv rl rr =>
        if hrsd : rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then
                .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l (.inner rls rlk rlv rll rlr)) rr
              else
                .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                  (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | leaf, _ => False.elim ✓
          | _, leaf => False.elim ✓
        else .inner (1 + ls + rs) k v l (inner rs rk rv rl rr)

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
    (hlr : BalanceLErasePrecond r.size l.size) : Impl α β :=
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
          | leaf, _ => False.elim ✓
          | _, leaf => False.elim ✓
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
## `balance` variants
-/

/-- Rebalances a tree after at most one element was added or removed from either subtree. -/
def balance (k : α) (v : β k) (l r : Impl α β) (hl : Balanced l) (hr : Balanced r)
    (h : BalancedAtRoot l.size r.size ∨
      BalancedAtRoot (l.size + 1) (r.size) ∨
      BalancedAtRoot (l.size) (r.size + 1) ∨
      (1 ≤ l.size ∧ BalancedAtRoot (l.size - 1) r.size) ∨
      (1 ≤ r.size ∧ BalancedAtRoot l.size (r.size - 1))) : Impl α β :=
  match l with
  | .leaf =>
    match r with
    | .leaf => .inner 1 k v .leaf .leaf
    | .inner _ _ _ .leaf .leaf => .inner 2 k v .leaf r
    | .inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | .inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | .inner rs rk rv (.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        if rls < ratio * rrs then
          .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf (.inner rls rlk rlv rll rlr)) rr
        else
          .inner (1 + rs) rlk rlv (.inner (1 + rll.size) k v .leaf rll)
            (.inner (1 + rrs + rlr.size) rk rv rlr rr)
  | .inner ls lk lv ll lr =>
    match r with
    | .leaf =>
      match ll, lr with
      | .leaf, .leaf => .inner 2 k v l .leaf
      | .leaf, .inner _ lrk lrv _ _ => .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf)
          (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .leaf => .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
      | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
        if lrs < ratio * lls then
          .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v (.inner lrs lrk lrv lrl lrr) .leaf)
        else
          .inner (1 + ls) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
            (.inner (1 + lrr.size) k v lrr .leaf)
    | .inner rs rk rv rl rr =>
      if h₁ : rs > delta * ls then
        match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
            if rls < ratio * rrs then
              .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
            else
              .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                (.inner (1 + rrs + rlr.size) rk rv rlr rr)
        | .leaf, _ => False.elim ✓
        | _, .leaf => False.elim ✓
      else if h₂ : ls > delta * rs then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
            if lrs < ratio * lls then
              .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
            else
              .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                (.inner (1 + rs + lrr.size) k v lrr r)
        | .leaf, _ => False.elim ✓
        | _, .leaf => False.elim ✓
      else
        .inner (1 + ls + rs) k v l r

@[tree_tac]
theorem size_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balance k v l r hrb hlb hlr).size = l.size + 1 + r.size := by
  simp only [balance.eq_def]; tree_tac

set_option maxHeartbeats 0 in
@[tree_tac]
theorem balanced_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    (balance k v l r hlb hrb hlr).Balanced := by
  sorry

/-- Slow version of `balance` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balance` are satisfied
(otherwise panics). -/
def balanceSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | .leaf =>
    match r with
    | .leaf => .inner 1 k v .leaf .leaf
    | .inner _ _ _ .leaf .leaf => .inner 2 k v .leaf r
    | .inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | .inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | .inner rs rk rv (.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        if rls < ratio * rrs then
          .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf (.inner rls rlk rlv rll rlr)) rr
        else
          .inner (1 + rs) rlk rlv (.inner (1 + rll.size) k v .leaf rll)
            (.inner (1 + rrs + rlr.size) rk rv rlr rr)
  | .inner ls lk lv ll lr =>
    match r with
    | .leaf =>
      match ll, lr with
      | .leaf, .leaf => .inner 2 k v l .leaf
      | .leaf, .inner _ lrk lrv _ _ => .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf)
          (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .leaf => .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
      | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
        if lrs < ratio * lls then
          .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v (.inner lrs lrk lrv lrl lrr) .leaf)
        else
          .inner (1 + ls) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
            (.inner (1 + lrr.size) k v lrr .leaf)
    | .inner rs rk rv rl rr =>
      if rs > delta * ls then
        match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
            if rls < ratio * rrs then
              .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
            else
              .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                (.inner (1 + rrs + rlr.size) rk rv rlr rr)
        | .leaf, _ => panic! "balanceSlow input was not balanced"
        | _, .leaf => panic! "balanceSlow input was not balanced"
      else if ls > delta * rs then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
            if lrs < ratio * lls then
              .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
            else
              .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                (.inner (1 + rs + lrr.size) k v lrr r)
        | .leaf, _ => panic! "balanceSlow input was not balanced"
        | _, .leaf => panic! "balanceSlow input was not balanced"
      else
        .inner (1 + ls + rs) k v l r

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
/-- A balanced tree of the given size. -/
structure Tree (size : Nat) where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced
  /-- The tree has size `size`. -/
  size_impl : impl.size = size

variable (α β) in
/-- A tuple of a key-value pair and a balanced tree of size `size`. -/
structure View (size : Nat) where
  /-- The key. -/
  k : α
  /-- The value. -/
  v : β k
  /-- The tree. -/
  tree : Tree α β size

attribute [tree_tac] Tree.balanced_impl Tree.size_impl

/-- Returns the tree `l ++ ⟨k, v⟩ ++ r`, with the smallest element chopped off. -/
def minView (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hlr : BalancedAtRoot l.size r.size) : View α β (l.size + r.size) :=
  match l with
  | leaf => ⟨k, v, ⟨r, hr, ✓⟩⟩
  | inner _ k' v' l' r' =>
      let d := minView k' v' l' r' ✓ ✓ ✓
      ⟨d.k, d.v, ⟨balanceRErase k v d.tree.impl r ✓ ✓
            (by simp only [tree_tac] at hl; tree_tac),
          ✓, by simp only [tree_tac] at hl; tree_tac⟩⟩

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
  | leaf => ⟨k, v, ⟨l, hl, ✓⟩⟩
  | inner _ k' v' l' r' =>
      let d := maxView k' v' l' r' ✓ ✓ ✓
      ⟨d.k, d.v, ⟨balanceLErase k v l d.tree.impl ✓ ✓
            (by simp only [tree_tac] at hr; tree_tac),
          ✓, by simp only [tree_tac] at hr; tree_tac⟩⟩

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

/-- Constructs the tree `l ++ r`. -/
@[inline]
def glue (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) (hlr : BalancedAtRoot l.size r.size) :
    Impl α β :=
  match l with
  | .leaf => r
  | l@hl₀:(.inner sz k v l' r') =>
    match r with
    | .leaf => l
    | r@hr₀:(.inner sz' k' v' l'' r'') =>
      if sz < sz' then
        let d := minView k' v' l'' r'' ✓ ✓ ✓
        balanceLErase d.k d.v l d.tree.impl (hl₀ ▸ hl) ✓
          (by simp only [tree_tac] at hl hr hlr; tree_tac)
      else
        let d := maxView k v l' r' ✓ ✓ ✓
        balanceRErase d.k d.v d.tree.impl r ✓ (hr₀ ▸ hr)
          (by simp only [tree_tac] at hl hr hlr; tree_tac)

@[tree_tac]
theorem size_glue {l r : Impl α β} {hl hr hlr} : (glue l r hl hr hlr).size = l.size + r.size := by
  simp only [glue]; tree_tac

@[tree_tac]
theorem balanced_glue {l r : Impl α β} {hl hr hlr} : (glue l r hl hr hlr).Balanced := by
  simp only [glue]; tree_tac

/-- Slower version of `glue` which can be used in the absence of balance information but still
assumes the preconditions of `glue`, otherwise might panic. -/
@[inline]
def glueSlow (l r : Impl α β) : Impl α β :=
  match l with
  | .leaf => r
  | l@(.inner sz k v l' r') =>
    match r with
    | .leaf => l
    | r@(.inner sz' k' v' l'' r'') =>
      if sz < sz' then
        let d := minViewSlow k' v' l'' r''
        balanceLSlow d.k d.v l d.tree
      else
        let d := maxViewSlow k v l' r'
        balanceRSlow d.k d.v d.tree r

/-!
## `insertMin` and `insertMax`
-/

/-- Inserts an element at the beginning of the tree. -/
def insertMin (k : α) (v : β k) (r : Impl α β) (hr : r.Balanced) : Tree α β (1 + r.size) :=
  match r with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | inner sz k' v' l' r' => ⟨balanceL k' v' (insertMin k v l' ✓).impl r'
      ✓ ✓ ✓, ✓, ✓⟩

/-- Slower version of `insertMin` which can be used in the absence of balance information but
still assumes the preconditions of `insertMin`, otherwise might panic. -/
def insertMinSlow (k : α) (v : β k) (r : Impl α β) : Impl α β :=
  match r with
  | leaf => .inner 1 k v .leaf .leaf
  | inner _ k' v' l' r' => balanceLSlow k' v' (insertMinSlow k v l') r'

/-- Inserts an element at the end of the tree. -/
def insertMax (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) : Tree α β (l.size + 1) :=
  match l with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | inner sz k' v' l' r' => ⟨balanceR k' v' l' (insertMax k v r' ✓).impl
      ✓ ✓ ✓, ✓, ✓⟩

/-- Slower version of `insertMax` which can be used in the absence of balance information but
still assumes the preconditions of `insertMax`, otherwise might panic. -/
def insertMaxSlow (k : α) (v : β k) (l : Impl α β) : Impl α β :=
  match l with
  | leaf => .inner 1 k v .leaf .leaf
  | inner _ k' v' l' r' => balanceRSlow k' v' l' (insertMaxSlow k v r')

/-!
## `link` and `link2`
-/

attribute [tree_tac] and_true true_and

set_option maxHeartbeats 0 in
/-- Builds the tree `l ++ ⟨k, v⟩ ++ r` without any balancing information at the root. -/
def link (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) :
    Tree α β (l.size + 1 + r.size) :=
  match l with
  | leaf =>
      let d := insertMin k v r ✓
      ⟨d.impl, ✓, ✓⟩
  | l@hl':(inner szl k' v' l' r') =>
      match r with
      | leaf =>
          let d := insertMax k v l ✓
          ⟨d.impl, ✓, ✓⟩
      | r@hr':(inner szr k'' v'' l'' r'') =>
          if h₁ : delta * szl < szr then
            ⟨balanceLErase k'' v'' (link k v l l'' ✓ ✓).impl r''
              ✓ ✓ ✓, ✓, ✓⟩
          else if h₂ : delta * szr < szl then
            ⟨balanceRErase k' v' l' (link k v r' r ✓ ✓).impl
              ✓ ✓ ✓, ✓, ✓⟩
          else
            ⟨.inner (l.size + 1 + r.size) k v l r, ✓, ✓⟩
  termination_by sizeOf l + sizeOf r

/-- Slower version of `link` which can be used in the absence of balance information but
still assumes the preconditions of `link`, otherwise might panic. -/
def linkSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => insertMinSlow k v r
  | l@(inner szl k' v' l' r') =>
      match r with
      | leaf => insertMaxSlow k v l
      | r@(inner szr k'' v'' l'' r'') =>
          if delta * szl < szr then
            balanceLSlow k'' v'' (linkSlow k v l l'') r''
          else if delta * szr < szl then
            balanceRSlow k' v' l' (linkSlow k v r r')
          else
            .inner (l.size + 1 + r.size) k v l r
  termination_by sizeOf l + sizeOf r

set_option maxHeartbeats 0 in
/-- Builds the tree `l ++ r` without any balancing information at the root. -/
def link2 (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) :
    Tree α β (l.size + r.size) :=
  match l with
  | leaf => ⟨r, ✓, ✓⟩
  | l@hl':(inner szl k' v' l' r') =>
      match r with
      | leaf => ⟨l, ✓, ✓⟩
      | r@hr':(inner szr k'' v'' l'' r'') =>
          if h₁ : delta * szl < szr then
            ⟨balanceLErase k'' v'' (link2 l l'' ✓ ✓).impl r'' ✓
              ✓ ✓, ✓, ✓⟩
          else if h₂ : delta * szr < szl then
            ⟨balanceRErase k' v' l' (link2 r' r ✓ ✓).impl ✓
              ✓ ✓, ✓, ✓⟩
          else
            ⟨glue l r ✓ ✓ ✓, ✓, ✓⟩
  termination_by sizeOf l + sizeOf r

/-- Slower version of `link2` which can be used in the absence of balance information but
still assumes the preconditions of `link2`, otherwise might panic. -/
def link2Slow (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => r
  | l@(inner szl k' v' l' r') =>
      match r with
      | leaf => l
      | r@(inner szr k'' v'' l'' r'') =>
          if delta * szl < szr then
            balanceLSlow k'' v'' (link2Slow l l'') r''
          else if delta * szr < szl then
            balanceRSlow k' v' l' (link2Slow r' r )
          else
            glueSlow l r
  termination_by sizeOf l + sizeOf r

/-!
## Modification operations
-/

-- TODO: inline annotations
-- TODO: rename slow to !

variable (α β) in
/-- A balanced tree of one of the given sizes. -/
structure Tree₂ (size₁ size₂ : Nat) where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced
  /-- The tree has size `size`. -/
  size_impl : impl.size = size₁ ∨ impl.size = size₂

attribute [tree_tac] Tree₂.balanced_impl

/-- An empty tree. -/
@[inline]
def empty : Impl α β :=
  .leaf

attribute [tree_tac] or_true true_or

/-- Adds a new mapping to the key, overwriting an existing one with equal key if present. -/
def insert [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Tree₂ α β l.size (l.size + 1) :=
  match l with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | inner sz k' v' l' r' =>
      match compare k k' with
      | .lt =>
          let ⟨d, hd, hd'⟩ := insert k v l' ✓
          ⟨balanceL k' v' d r' ✓ ✓ ✓, ✓, ✓⟩
      | .gt =>
          let ⟨d, hd, hd'⟩ := insert k v r' ✓
          ⟨balanceR k' v' l' d ✓ ✓ ✓, ✓, ✓⟩
      | .eq => ⟨.inner sz k v l' r', ✓, ✓⟩

/-- Slower version of `insert` which can be used in the absence of balance information but
still assumes the preconditions of `insert`, otherwise might panic. -/
def insertSlow [Ord α] (k : α) (v : β k) (l : Impl α β) : Impl α β :=
  match l with
  | leaf => .inner 1 k v .leaf .leaf
  | inner sz k' v' l r =>
      match compare k k' with
      | .lt => balanceLSlow k' v' (insertSlow k v l) r
      | .gt => balanceRSlow k' v' l (insertSlow k v r)
      | .eq => .inner sz k v l r

/-- Returns the pair `(l.contains k, l.insert k v)`. -/
@[inline]
def containsThenInsert [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Bool × Tree₂ α β l.size (l.size + 1) :=
  let sz := size l
  let m := l.insert k v hl
  (sz == m.1.size, m)
where -- workaround for https://github.com/leanprover/lean4/issues/6058
  size : Impl α β → Nat
  | leaf => 0
  | inner sz _ _ _ _ => sz

/-- Slower version of `containsThenInsert` which can be used in the absence of balance
information but still assumes the preconditions of `containsThenInsert`, otherwise might panic. -/
@[inline]
def containsThenInsertSlow [Ord α] (k : α) (v : β k) (l : Impl α β) :
    Bool × Impl α β :=
  let sz := size l
  let m := l.insertSlow k v
  (sz == m.size, m)
where -- workaround for https://github.com/leanprover/lean4/issues/6058
  size : Impl α β → Nat
  | leaf => 0
  | inner sz _ _ _ _ => sz

/-- Adds a new mapping to the key, overwriting an existing one with equal key if present. -/
@[inline]
def insertIfNew [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Tree₂ α β l.size (l.size + 1) :=
  if l.contains k then ⟨l, ✓, ✓⟩ else l.insert k v ✓

/-- Slower version of `insertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `insertIfNew`, otherwise might panic. -/
@[inline]
def insertIfNewSlow [Ord α] (k : α) (v : β k) (l : Impl α β) :
    Impl α β :=
  if l.contains k then l else l.insertSlow k v

/-- Returns the pair `(l.contains k, l.insertIfNew k v)`. -/
@[inline]
def containsThenInsertIfNew [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Bool × Tree₂ α β l.size (l.size + 1) :=
  if l.contains k then (true, ⟨l, ✓, ✓⟩) else (false, l.insert k v ✓)

/-- Slower version of `containsThenInsertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `containsThenInsertIfNew`, otherwise might panic. -/
@[inline]
def containsThenInsertIfNewSlow [Ord α] (k : α) (v : β k) (l : Impl α β) :
    Bool × Impl α β :=
  if l.contains k then (true, l) else (false, l.insertSlow k v)

/-- Removes the mapping with key `k`, if it exists. -/
def erase [Ord α] (l : Impl α β) (k : α) (h : l.Balanced) : Tree₂ α β l.size (l.size - 1) :=
  match l with
  | leaf => ⟨.leaf, ✓, ✓⟩
  | inner sz k' v' l r =>
    match compare k k' with
    | .lt =>
      let ⟨l', hl'₁, hl'₂⟩ := erase l k ✓
      ⟨balanceRErase k' v' l' r ✓ ✓ ✓, ✓, ✓⟩
    | .gt =>
      let ⟨r', hr'₁, hr'₂⟩ := erase r k ✓
      ⟨balanceLErase k' v' l r' ✓ ✓ ✓, ✓, ✓⟩
    | .eq => ⟨glue l r ✓ ✓ ✓, ✓, ✓⟩

/-- Slower version of `erase` which can be used in the absence of balance
information but still assumes the preconditions of `erase`, otherwise might panic. -/
def eraseSlow [Ord α] (l : Impl α β) (k : α) : Impl α β :=
  match l with
  | leaf => .leaf
  | inner _ k' v' l r =>
    match compare k k' with
    | .lt => balanceRSlow k' v' (eraseSlow l k) r
    | .gt => balanceLSlow k' v' l (eraseSlow r k)
    | .eq => glueSlow l r

variable (α β) in
/-- A balanced tree. -/
structure BImpl where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced

attribute [tree_tac] BImpl.balanced_impl

/-- Returns the tree consisting of the mappings `(k, (f k v).get)` where `(k, v)` was a mapping in
the original tree and `(f k v).isSome`. -/
@[specialize]
def filterMap [Ord α] (f : (a : α) → β a → Option (γ a)) (l : Impl α β) (hl : l.Balanced) :
    BImpl α γ :=
  match l with
  | .leaf => ⟨.leaf, ✓⟩
  | .inner sz k v l r =>
    match f k v with
    | none => ⟨(link2 (filterMap f l ✓).impl (filterMap f r ✓).impl ✓ ✓).impl, ✓⟩
    | some v' => ⟨(link k v' (filterMap f l ✓).impl (filterMap f r ✓).impl ✓ ✓).impl, ✓⟩

/-- Slower version of `filterMap` which can be used in the absence of balance
information but still assumes the preconditions of `filterMap`, otherwise might panic. -/
@[specialize]
def filterMapSlow [Ord α] (f : (a : α) → β a → Option (γ a)) (l : Impl α β) : Impl α γ :=
  match l with
  | .leaf => .leaf
  | .inner _ k v l r =>
    match f k v with
    | none => link2Slow (filterMapSlow f l) (filterMapSlow f r)
    | some v' => linkSlow k v' (filterMapSlow f l) (filterMapSlow f r)

/-- Returns the tree consisting of the mappings `(k, f k v)` where `(k, v)` was a mapping in the
original tree. -/
@[specialize]
def map [Ord α] (f : (a : α) → β a → γ a) (l : Impl α β) : Impl α γ :=
  match l with
  | .leaf => .leaf
  | .inner sz k v l r => .inner sz k (f k v) (map f l) (map f r)

/-- Returns the tree consisting of the mapping `(k, v)` where `(k, v)` was a mapping in the
original tree and `f k v = true`. -/
@[specialize]
def filter [Ord α] (f : (a : α) → β a → Bool) (l : Impl α β) (hl : Balanced l) : BImpl α β :=
  match l with
  | .leaf => ⟨.leaf, ✓⟩
  | .inner sz k v l r =>
    match f k v with
    | false => ⟨(link2 (filter f l ✓).impl (filter f r ✓).impl ✓ ✓).impl, ✓⟩
    | true => ⟨(link k v (filter f l ✓).impl (filter f r ✓).impl ✓ ✓).impl, ✓⟩

/-- Slower version of `filter` which can be used in the absence of balance
information but still assumes the preconditions of `filter`, otherwise might panic. -/
@[specialize]
def filterSlow [Ord α] (f : (a : α) → β a → Bool) (l : Impl α β) : Impl α β :=
  match l with
  | .leaf => .leaf
  | .inner _ k v l r =>
    match f k v with
    | false => link2Slow (filterSlow f l) (filterSlow f r)
    | true => linkSlow k v (filterSlow f l) (filterSlow f r)

variable (α β) in
/-- A balanced tree of one of the given sizes. -/
structure Tree₃ (size₁ size₂ size₃ : Nat) where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced
  /-- The tree has size `size`. -/
  size_impl : impl.size = size₁ ∨ impl.size = size₂ ∨ impl.size = size₃

namespace Const

-- TODO: unify indentation

/-- Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it. -/
def modify [Ord α] (k : α) (f : Option δ → Option δ) (l : Impl α (fun _ => δ)) (hl : l.Balanced) :
    Tree₃ α (fun _ => δ) (l.size - 1) l.size (l.size + 1) :=
  match l with
  | .leaf =>
    match f none with
    | none => ⟨.leaf, ✓, ✓⟩
    | some v => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | .inner sz k' v' l' r' =>
    match compare k k' with
    | .lt =>
        let ⟨d, hd, hd'⟩ := modify k f l' ✓
        ⟨balance k' v' d r' ✓ ✓ ✓, ✓, ✓⟩
    | .gt =>
        let ⟨d, hd, hd'⟩ := modify k f r' ✓
        ⟨balance k' v' l' d ✓ ✓ ✓, ✓, ✓⟩
    | .eq =>
      match f (some v') with
      | none => ⟨glue l' r' ✓ ✓ ✓, ✓, ✓⟩
      | some v => ⟨.inner sz k' v l' r', ✓, ✓⟩

/-- Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic. -/
def modifySlow [Ord α] (k : α) (f : Option δ → Option δ) (l : Impl α (fun _ => δ)) :
    Impl α (fun _ => δ) :=
  match l with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match compare k k' with
    | .lt => balanceSlow k' v' (modifySlow k f l') r'
    | .gt => balanceSlow k' v' l' (modifySlow k f r')
    | .eq =>
      match f (some v') with
      | none => glueSlow l' r'
      | some v => .inner sz k' v l' r'

end Const

/-- Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it.
This version of the function requires `LawfulEqOrd α`. There is an alternative non-dependent version
called `Const.modify`. -/
def modify [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (l : Impl α β)
    (hl : l.Balanced) : Tree₃ α β (l.size - 1) l.size (l.size + 1) :=
  match l with
  | .leaf =>
    match f none with
    | none => ⟨.leaf, ✓, ✓⟩
    | some v => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | .inner sz k' v' l' r' =>
    match h : compare k k' with
    | .lt =>
        let ⟨d, hd, hd'⟩ := modify k f l' ✓
        ⟨balance k' v' d r' ✓ ✓ ✓, ✓, ✓⟩
    | .gt =>
        let ⟨d, hd, hd'⟩ := modify k f r' ✓
        ⟨balance k' v' l' d ✓ ✓ ✓, ✓, ✓⟩
    | .eq =>
      match f (some (cast (congrArg β (eq_of_compare h).symm) v')) with
      | none => ⟨glue l' r' ✓ ✓ ✓, ✓, ✓⟩
      | some v => ⟨.inner sz k v l' r', ✓, ✓⟩

/-- Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic. -/
def modifySlow [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (l : Impl α β)
    : Impl α β :=
  match l with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match h : compare k k' with
    | .lt => balanceSlow k' v' (modifySlow k f l') r'
    | .gt => balanceSlow k' v' l' (modifySlow k f r')
    | .eq =>
      match f (some (cast (congrArg β (eq_of_compare h).symm) v')) with
      | none => glueSlow l' r'
      | some v => .inner sz k v l' r'

/-- If the tree contains a mapping `(k', v)` with `k == k'`, adjust it to have mapping
`(k', f k' v h)`, which `h : compare k k' = .eq`. If no such mapping is present, returns the
tree unmodified. Note that this function is likely to be faster than `modify` because it never
needs to rebalance the tree. -/
def adjust [Ord α] (k : α) (f : (k' : α) → β k' → (compare k k' = .eq) → β k') (l : Impl α β) :
    Impl α β :=
  match l with
  | .leaf => .leaf
  | .inner sz k' v' l r =>
    match h : compare k k' with
    | .lt => .inner sz k' v' (adjust k f l) r
    | .gt => .inner sz k' v' l (adjust k f r)
    | .eq => .inner sz k' (f k' v' h) l r

end Impl

end Std.DOrderedTree.Internal
