/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.Classes.LawfulEqOrd
import Orderedtree.DOrderedTree.Internal.Impl.Attr
import Orderedtree.Classes.TransOrd
import Lean.Elab.Tactic

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}

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

/-- The smallest element of `l` that is not less than `k`. Also known as `lookupGE` or `ceil`. -/
@[inline]
def lowerBound? [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .lt => go (some ⟨ky, y⟩) l
    | .eq => some ⟨ky, y⟩
    | .gt => go best r

/-- The smallest element of `l` that is greater than `k`. Also known as `lookupGT` or `higher`. -/
@[inline]
def upperBound? [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .lt => go (some ⟨ky, y⟩) l
    | _ => go best r

/-- The largest element of `l` that is not greater than `k`. Also known as `floor`. -/
@[inline]
def lookupLE [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .lt => go best l
    | .eq => some ⟨ky, y⟩
    | .gt => go (some ⟨ky, y⟩) r

/-- The largest element of `l` that is less than `k`. Also known as `lower`. -/
@[inline]
def lookupLT [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .gt => go (some ⟨ky, y⟩) r
    | _ => go best l

/-- The smallest element of `l`. -/
def min? [Ord α] : Impl α β → Option ((a : α) × β a)
  | .leaf => none
  | .inner _ k v .leaf _ => some ⟨k, v⟩
  | .inner _ _ _ l@(.inner _ _ _ _ _) _ => l.min?

/-- The largest element of `l`. -/
def max? [Ord α] : Impl α β → Option ((a : α) × β a)
  | .leaf => none
  | .inner _ k v _ .leaf => some ⟨k, v⟩
  | .inner _ _ _ _ r@(.inner _ _ _ _ _) => r.max?

/-- Returns the mapping with the `n`-th smallest key, or `none` if `n` is at least `l.size`. -/
def atIndex? [Ord α] : Impl α β → Nat → Option ((a : α) × β a)
  | .leaf, _ => none
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => l.atIndex? n
    | .eq => some ⟨k, v⟩
    | .gt => r.atIndex? (n - l.size - 1)

/-- Returns the mapping with the `n`-th smallest key, or panics if `n` is at least `l.size`. -/
def atIndex! [Ord α] [Inhabited ((a : α) × β a)] : Impl α β → Nat → (a : α) × β a
  | .leaf, _ => panic! "Out-of-bounds access"
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => l.atIndex! n
    | .eq => ⟨k, v⟩
    | .gt => r.atIndex! (n - l.size - 1)

/-- Returns the mapping with the `n`-th smallest key, or `fallback` if `n` is at least `l.size`. -/
def atIndexD [Ord α] : Impl α β → Nat → (a : α) × β a → (a : α) × β a
  | .leaf, _, fallback => fallback
  | .inner _ k v l r, n, fallback =>
    match compare n l.size with
    | .lt => l.atIndexD n fallback
    | .eq => ⟨k, v⟩
    | .gt => r.atIndexD (n - l.size - 1) fallback

/-- Returns the number of mappings whose key is strictly less than `k`. -/
@[inline]
def indexOf [Ord α] (k : α) : Impl α β → Nat :=
  go 0
where
  go (sofar : Nat) : Impl α β → Nat
  | .leaf => sofar
  | .inner _ ky _ l r =>
    match compare k ky with
    | .lt => go sofar l
    | .eq => sofar
    | .gt => go (l.size + 1 + sofar) r

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
elab "as_aux_lemma" " => " s:tacticSeq : tactic => liftMetaTactic fun mvarId => do
  let (mvars, _) ← runTactic mvarId s
  unless mvars.isEmpty do
    throwError "Left-over goals, cannot abstract"
  let e ← instantiateMVars (mkMVar mvarId)
  let e ← mkAuxTheorem (`Std.DOrderedTree.Internal.Impl ++ (← mkFreshUserName `test)) (← mvarId.getType) e
  mvarId.assign e
  return []

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
    subst_eqs
    omega
  ))

/-- (Implementation detail) -/
scoped macro "✓" : term => `(term| by as_aux_lemma => tree_tac)

end

theorem BalanceLPrecond.erase {left right : Nat} :
    BalanceLPrecond left right → BalanceLErasePrecond left right := by
  tree_tac

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
        if hlsd : delta * rs < ls then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v (inner lrs lrk lrv lrl lrr) r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | inner _ _ _ _ _, leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v (.inner ls lk lv ll lr) r

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
        .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v lr .leaf)
  | (inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | (inner ls lk lv ll lr) =>
        if hlsd : delta * rs < ls then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then
                .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else
                .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                  (.inner (1 + rs + lrr.size) k v lrr r)
          | inner _ _ _ _ _, leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v l r

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
    | inner ls lk lv ll@(.inner _ _ _ _ _) lr@(.inner lrs _ _ _ _) =>
        .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v lr .leaf)
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
          | inner _ _ _ _ _, leaf => panic! "balanceLSlow input was not balanced"
          | leaf, _ => panic! "balanceLSlow input was not balanced"
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
          | inner _ _ _ _ _, leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v l (inner rs rk rv rl rr)

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
        .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
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
          | inner _ _ _ _ _ , leaf => False.elim ✓
          | leaf, _ => False.elim ✓
        else .inner (1 + ls + rs) k v l r

/-- Slow version of `balanceR` which can be used in the complete absence of balancing information
but still assumes that the preconditions of `balanceR` or `balanceRErase` are satisfied
(otherwise panics). -/
@[inline]
def balanceRSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | inner _ _ _ .leaf .leaf => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls _ _ _ _) rr@(.inner _ _ _ _ _) =>
        .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
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
          | inner _ _ _ _ _, leaf => panic! "balanceRSlow input was not balanced"
          | leaf, _ => panic! "balanceRSlow input was not balanced"
        else .inner (1 + ls + rs) k v l r

/-!
## `balance` variants
-/

/-- Rebalances a tree after at most one element was added or removed from either subtree. -/
def balance (k : α) (v : β k) (l r : Impl α β) (hl : Balanced l) (hr : Balanced r)
    (h : BalanceLErasePrecond l.size r.size ∨
      BalanceLErasePrecond r.size l.size) : Impl α β :=
  match l with
  | .leaf =>
    match r with
    | .leaf => .inner 1 k v .leaf .leaf
    | .inner _ _ _ .leaf .leaf => .inner 2 k v .leaf r
    | .inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | .inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf)
        (.inner 1 rk rv .leaf .leaf)
    | .inner rs rk rv (.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf (.inner rls rlk rlv rll rlr)) rr
  | .inner ls lk lv ll lr =>
    match r with
    | .leaf =>
      match ll, lr with
      | .leaf, .leaf => .inner 2 k v l .leaf
      | .leaf, .inner _ lrk lrv _ _ => .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf)
          (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .leaf => .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
      | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
          .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v (.inner lrs lrk lrv lrl lrr) .leaf)
    | .inner rs rk rv rl rr =>
      if h₁ : delta * ls < rs then
        match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
            if rls < ratio * rrs then
              .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
            else
              .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                (.inner (1 + rrs + rlr.size) rk rv rlr rr)
        | inner _ _ _ _ _, .leaf => False.elim ✓
        | .leaf, _ => False.elim ✓
      else if h₂ : delta * rs < ls then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
            if lrs < ratio * lls then
              .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
            else
              .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                (.inner (1 + rs + lrr.size) k v lrr r)
        | inner _ _ _ _ _, .leaf => False.elim ✓
        | .leaf, _ => False.elim ✓
      else
        .inner (1 + ls + rs) k v l r

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
    | .inner rs rk rv (.inner rls rlk rlv rll rlr) rr@(.inner _ _ _ _ _) =>
          .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf (.inner rls rlk rlv rll rlr)) rr
  | .inner ls lk lv ll lr =>
    match r with
    | .leaf =>
      match ll, lr with
      | .leaf, .leaf => .inner 2 k v l .leaf
      | .leaf, .inner _ lrk lrv _ _ => .inner 3 lrk lrv (.inner 1 lk lv .leaf .leaf)
          (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .leaf => .inner 3 lk lv ll (.inner 1 k v .leaf .leaf)
      | .inner _ _ _ _ _, .inner lrs lrk lrv lrl lrr =>
          .inner (1 + ls) lk lv ll (.inner (1 + lrs) k v (.inner lrs lrk lrv lrl lrr) .leaf)
    | .inner rs rk rv rl rr =>
      if rs > delta * ls then
        match rl, rr with
        | .inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
            if rls < ratio * rrs then
              .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
            else
              .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll)
                (.inner (1 + rrs + rlr.size) rk rv rlr rr)
        | inner _ _ _ _ _, .leaf => panic! "balanceSlow input was not balanced"
        | .leaf, _ => panic! "balanceSlow input was not balanced"
      else if ls > delta * rs then
        match ll, lr with
        | .inner lls _ _ _ _, .inner lrs lrk lrv lrl lrr =>
            if lrs < ratio * lls then
              .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
            else
              .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl)
                (.inner (1 + rs + lrr.size) k v lrr r)
        | inner _ _ _ _ _, .leaf => panic! "balanceSlow input was not balanced"
        | .leaf, _ => panic! "balanceSlow input was not balanced"
      else
        .inner (1 + ls + rs) k v l r

@[simp]
theorem balancedAtRoot_zero_zero : BalancedAtRoot 0 0 := by
  simp only [BalancedAtRoot]; omega

@[simp]
theorem balancedAtRoot_zero_one : BalancedAtRoot 0 1 := by
  simp only [BalancedAtRoot]; omega

@[simp]
theorem balancedAtRoot_one_zero : BalancedAtRoot 1 0 := by
  simp only [BalancedAtRoot]; omega

@[simp]
theorem balancedAtRoot_one_one : BalancedAtRoot 1 1 := by
  simp only [BalancedAtRoot, delta]; omega

@[simp]
theorem balancedAtRoot_two_one : BalancedAtRoot 2 1 := by
  simp only [BalancedAtRoot, delta]; omega

@[simp]
theorem balancedAtRoot_one_two : BalancedAtRoot 1 2 := by
  simp only [BalancedAtRoot, delta]; omega

theorem balanced_one_leaf_leaf {k : α} {v : β k} : (inner 1 k v leaf leaf).Balanced :=
  balanced_inner_iff.2 ⟨.leaf, .leaf, by simp [size_leaf], by simp [size_leaf]⟩

theorem balancedAtRoot_zero_iff {n : Nat} : BalancedAtRoot 0 n ↔ n ≤ 1 := by
  simp only [BalancedAtRoot]; omega

theorem balancedAtRoot_zero_iff' {n : Nat} : BalancedAtRoot n 0 ↔ n ≤ 1 := by
  simp only [BalancedAtRoot]; omega

theorem Balanced.one_le {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → 1 ≤ sz := by
  tree_tac

theorem Balanced.eq {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → sz = l.size + 1 + r.size
  | .inner _ _ _ h => h

theorem Balanced.left {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → l.Balanced
  | .inner h _ _ _ => h

theorem Balanced.right {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced → r.Balanced
  | .inner _ h _ _ => h

theorem Balanced.at_root {sz k v l r} : (Impl.inner sz k v l r : Impl α β).Balanced →
    BalancedAtRoot l.size r.size
  | .inner _ _ h _ => h

theorem BalancedAtRoot.symm {l r : Nat} : BalancedAtRoot l r → BalancedAtRoot r l := by
  tree_tac

theorem BalancedAtRoot.erase_left {l l' r : Nat} : BalancedAtRoot l r → l - 1 ≤ l' → l' ≤ l →
    BalanceLErasePrecond r l' := by tree_tac

theorem BalancedAtRoot.erase_right {l r r' : Nat} : BalancedAtRoot l r → r - 1 ≤ r' → r' ≤ r →
    BalanceLErasePrecond l r' :=
  fun h h₁ h₂ => h.symm.erase_left h₁ h₂

theorem BalancedAtRoot.adjust_left {l l' r : Nat} : BalancedAtRoot l r → l - 1 ≤ l' → l' ≤ l + 1 →
    BalanceLErasePrecond l' r ∨ BalanceLErasePrecond r l' := by tree_tac

theorem BalancedAtRoot.adjust_right {l r r' : Nat} : BalancedAtRoot l r → r - 1 ≤ r' → r' ≤ r + 1 →
    BalanceLErasePrecond l r' ∨ BalanceLErasePrecond r' l :=
  fun h h₁ h₂ => h.symm.adjust_left h₁ h₂ |>.symm

theorem balanceLErasePrecond_zero_iff {n : Nat} : BalanceLErasePrecond 0 n ↔ n ≤ 1 := by
  tree_tac

theorem balanceLErasePrecond_zero_iff' {n : Nat} : BalanceLErasePrecond n 0 ↔ n ≤ 3 := by
  tree_tac

theorem omega_fact_1 {n m : Nat} (h₂ : n + 1 + m ≤ 3) (h₃ : 1 ≤ n) (h₄ : 1 ≤ m) :
    n = 1 ∧ m = 1 := by omega

theorem omega_fact_2 {ls rls rrs : Nat} (h₁ : rls < 2 * rrs)
    (h₂ : BalanceLErasePrecond (rls + 1 + rrs) ls) (h₃ : 1 ≤ ls) : rls ≤ 3 * ls := by
  dsimp only [tree_tac] at *
  omega

/-- Constructor for an inner node with the correct size. -/
@[tree_tac]
def bin (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  .inner (l.size + 1 + r.size) k v l r

/-- A single left rotation. -/
@[tree_tac]
def singleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rl rr : Impl α β) : Impl α β :=
  bin rk rv (bin k v l rl) rr

/-- A single right rotation. -/
@[tree_tac]
def singleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll lr : Impl α β) (r : Impl α β) : Impl α β :=
  bin lk lv ll (bin k v lr r)

/-- A double left rotation. -/
@[tree_tac]
def doubleL (k : α) (v : β k) (l : Impl α β) (rk : α) (rv : β rk) (rlk : α) (rlv : β rlk)
    (rll rlr : Impl α β) (rr : Impl α β) : Impl α β :=
  bin rlk rlv (bin k v l rll) (bin rk rv rlr rr)

/-- A double right rotation. -/
@[tree_tac]
def doubleR (k : α) (v : β k) (lk : α) (lv : β lk) (ll : Impl α β) (lrk : α) (lrv : β lrk)
    (lrl lrr : Impl α β) (r : Impl α β) : Impl α β :=
  bin lrk lrv (bin lk lv ll lrl) (bin k v lrr r)

theorem Balanced.map {l₁ l₂ : Impl α β} : l₁.Balanced → l₁ = l₂ → l₂.Balanced
  | h, rfl => h

attribute [tree_tac] and_true true_and

theorem balanced_singleL (k v l rs rk rv rl rr) (hl : l.Balanced)
    (hr : (Impl.inner rs rk rv rl rr).Balanced)
    (hlr : BalanceLErasePrecond l.size rs ∨ BalanceLErasePrecond rs l.size)
    (hh : rs > delta * l.size)
    (hx : rl.size < ratio * rr.size) :
    (singleL k v l rk rv rl rr : Impl α β).Balanced := by
  tree_tac

theorem balanced_singleR (k v ls lk lv ll lr r) (hl : (Impl.inner ls lk lv ll lr).Balanced)
    (hr : r.Balanced) (hlr : BalanceLErasePrecond ls r.size ∨ BalanceLErasePrecond r.size ls)
    (hh : ls > delta * r.size)
    (hx : lr.size < ratio * ll.size) :
    (singleR k v lk lv ll lr r : Impl α β).Balanced := by
  tree_tac

theorem balanced_doubleL (k v l rs rk rv rls rlk rlv rll rlr) (rr : Impl α β) (hl : l.Balanced)
    (hr : (Impl.inner rs rk rv (Impl.inner rls rlk rlv rll rlr) rr).Balanced)
    (hlr : BalanceLErasePrecond l.size rs ∨ BalanceLErasePrecond rs l.size)
    (hh : rs > delta * l.size) (hx : ¬rls < ratio * rr.size) :
    (doubleL k v l rk rv rlk rlv rll rlr rr).Balanced := by
  tree_tac

theorem balanced_doubleR (k v ls lk lv ll lrs lrk lrv lrl lrr) (r : Impl α β)
    (hl : (Impl.inner ls lk lv ll (Impl.inner lrs lrk lrv lrl lrr)).Balanced) (hr : r.Balanced)
    (hlr : BalanceLErasePrecond ls r.size ∨ BalanceLErasePrecond r.size ls)
    (hh : ls > delta * r.size) (hx : ¬lrs < ratio * ll.size) :
    (doubleR k v lk lv ll lrk lrv lrl lrr r).Balanced := by
  tree_tac

theorem balanceSlow_desc {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balanceSlow k v l r).size = l.size + 1 + r.size ∧ (balanceSlow k v l r).Balanced := by
  cases k, v, l, r using balanceSlow.fun_cases
  all_goals
    simp only [balanceSlow, *, if_true, if_false, true_and, size_inner, size_leaf,
      balanced_one_leaf_leaf]

  -- Group 1: l = leaf
  · rename_i sz k' v'
    obtain rfl : sz = 1 := by tree_tac
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨.leaf, balanced_one_leaf_leaf, by simp [size_leaf, size_inner],
      by simp only [tree_tac]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hrb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff] at hrb
    obtain rfl : sz' = 1 := Nat.le_antisymm hrb.2.2.1 hrb.2.1.one_le
    obtain rfl : sz = 2 := by simp [hrb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, hrb.2.1, by simp [size_inner],
      by simp [size_inner]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hrb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff'] at hrb
    obtain rfl : sz' = 1 := Nat.le_antisymm hrb.2.2.1 hrb.1.one_le
    obtain rfl : sz = 2 := by simp [hrb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, balanced_one_leaf_leaf, by simp [size_inner],
      by simp [size_inner]⟩
  · rw [balanced_inner_iff, size_inner, size_inner] at hrb
    obtain rfl := hrb.2.2.2
    simp only [size_inner, size_leaf, balanceLErasePrecond_zero_iff, balanceLErasePrecond_zero_iff'] at hlr ⊢
    rw [or_iff_right_of_imp (fun h => Nat.le_trans h (by decide))] at hlr
    simp only [ratio] at *
    rename_i rls rrs _ _ _ _ _ _ _ _ _ _
    obtain ⟨rfl, rfl⟩ : rls = 1 ∧ rrs = 1 := omega_fact_1 hlr hrb.1.one_le hrb.2.1.one_le
    refine balanced_inner_iff.2 ⟨?_, hrb.2.1, by simp [size_inner], by simp [size_inner, Nat.add_assoc]⟩
    refine balanced_inner_iff.2 ⟨.leaf, hrb.1, ?_, by simp [size_leaf, size_inner]⟩
    simp [size_leaf, size_inner]

  -- Group 2: r = leaf
  · rename_i sz k' v'
    obtain rfl : sz = 1 := by tree_tac
    simp only [Nat.reduceAdd, Nat.add_zero, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, .leaf, by simp [size_leaf, size_inner],
      by simp [size_leaf, size_inner]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hlb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff] at hlb
    obtain rfl : sz' = 1 := Nat.le_antisymm hlb.2.2.1 hlb.2.1.one_le
    obtain rfl : sz = 2 := by simp [hlb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨balanced_one_leaf_leaf, balanced_one_leaf_leaf, by simp [size_inner],
      by simp [size_inner]⟩
  · rename_i sz sz' rk k' rv v' l r
    rw [balanced_inner_iff] at hlb
    simp only [size_leaf, size_inner, balancedAtRoot_zero_iff'] at hlb
    obtain rfl : sz' = 1 := Nat.le_antisymm hlb.2.2.1 hlb.1.one_le
    obtain rfl : sz = 2 := by simp [hlb.2.2]
    simp only [Nat.zero_add, Nat.reduceAdd, true_and]
    exact balanced_inner_iff.2 ⟨hlb.1, balanced_one_leaf_leaf, by simp [size_inner],
      by simp [size_inner]⟩
  · rw [balanced_inner_iff, size_inner, size_inner] at hlb
    obtain rfl := hlb.2.2.2
    simp only [size_inner, size_leaf, balanceLErasePrecond_zero_iff, balanceLErasePrecond_zero_iff'] at hlr ⊢
    rw [or_iff_left_of_imp (fun h => Nat.le_trans h (by decide))] at hlr
    simp only [ratio] at *
    rename_i rls rrs _ _ _ _ _ _ _ _ _ _
    obtain ⟨rfl, rfl⟩ : rls = 1 ∧ rrs = 1 := omega_fact_1 hlr hlb.1.one_le hlb.2.1.one_le
    simp only [Nat.reduceAdd, Nat.add_zero, true_and]
    refine balanced_inner_iff.2 ⟨hlb.1, ?_, by simp [size_inner], by simp [size_inner, Nat.add_assoc]⟩
    refine balanced_inner_iff.2 ⟨hlb.2.1, .leaf, ?_, by simp [size_leaf, size_inner]⟩
    simp [size_leaf, size_inner]

  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs hlsrs rls rrs hrlsrrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_singleL k v _ _ _ _ _ _ hlb hrb hlr hlsrs hrlsrrs).map ?_
    simp only [singleL, bin]
    congr 1
    · simp only [size_inner, hrb.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl

  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs hlsrs rls rrs hrlsrrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_doubleL k v _ _ _ _ _ _ _ _ _ _ hlb hrb hlr hlsrs hrlsrrs).map ?_
    simp only [doubleL, bin]
    congr 1
    · simp only [size_inner, hrb.eq, hrb.left.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl

  · exfalso
    rename_i ls rs h rls _ _ _ _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff'] at hrb
    simp only [delta] at h
    have := hlb.one_le
    omega
  · exfalso
    rename_i ls rs h _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff] at hrb
    simp only [delta] at h
    have := hlb.one_le
    omega
  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs _ hlsrs lls lrs hllslrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_singleR k v _ _ _ _ _ _ hlb hrb hlr hlsrs hllslrs).map ?_
    simp only [singleR, bin]
    congr 1
    · simp only [size_inner, hlb.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
  ·
    refine ⟨by ac_rfl, ?_⟩
    rename_i ls rs _ hlsrs lls lrs hllslrs _ _ _ _ _ _ _ _ _ _ _ _ _ _
    refine (balanced_doubleR k v _ _ _ _ _ _ _ _ _ _ hlb hrb hlr hlsrs hllslrs).map ?_
    simp only [doubleR, bin]
    congr 1
    · simp only [size_inner, hlb.eq, hlb.right.eq]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
    · congr 1
      simp only [size_inner]
      ac_rfl
  · exfalso
    rename_i ls rs h rls _ _ _ _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff'] at hlb
    simp only [delta] at h
    have := hrb.one_le
    omega
  · exfalso
    rename_i ls rs h _ _ _ _ _ _ _
    simp only [balanced_inner_iff, size_inner, size_leaf, balancedAtRoot_zero_iff] at hlb
    simp only [delta] at h
    have := hrb.one_le
    omega
  · refine ⟨by ac_rfl, .inner hlb hrb (Or.inr ⟨?_, ?_⟩) (by simp only [size_inner]; ac_rfl)⟩
    · rwa [size_inner, size_inner, ← Nat.not_lt]
    · rwa [size_inner, size_inner, ← Nat.not_lt]

theorem balanceL_eq_balanceLErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balanceLErase k v l r hlb hrb hlr.erase := by
  rw [balanceL.eq_def, balanceLErase.eq_def]
  split
  · dsimp only
    split
    all_goals dsimp only
    contradiction
  · dsimp only
    split
    all_goals dsimp only
    split
    · split
      · dsimp only
      · contradiction
      · contradiction
    · rfl

theorem balanceLErase_eq_balanceLSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceLErase k v l r hlb hrb hlr = balanceLSlow k v l r := by
  rw [balanceLErase.eq_def, balanceLSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balanceLSlow_eq_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced)
    (hrb : r.Balanced) (hlr : BalanceLErasePrecond l.size r.size) :
    balanceLSlow k v l r = balanceSlow k v l r := by
  cases k, v, l, r using balanceSlow.fun_cases
  all_goals
    simp only [balanceLSlow, balanceSlow, *, if_true, if_false, true_and, size_inner, size_leaf]
  all_goals try rfl
  all_goals try contradiction
  all_goals try (exfalso; tree_tac; done)
  all_goals congr; tree_tac

theorem balanceR_eq_balanceRErase {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balanceRErase k v l r hlb hrb hlr.erase := by
  rw [balanceR.eq_def, balanceRErase.eq_def]
  split
  · dsimp only
    split
    all_goals dsimp only
    contradiction
  · dsimp only
    split
    all_goals dsimp only
    split
    · split
      · dsimp only
      · contradiction
      · contradiction
    · rfl

theorem balanceRErase_eq_balanceRSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceRErase k v l r hlb hrb hlr = balanceRSlow k v l r := by
  rw [balanceRErase.eq_def, balanceRSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

theorem balanceRSlow_eq_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced)
    (hrb : r.Balanced) (hlr : BalanceLErasePrecond r.size l.size) :
    balanceRSlow k v l r = balanceSlow k v l r := by
  cases k, v, l, r using balanceSlow.fun_cases
  all_goals
    simp only [balanceRSlow, balanceSlow, *, if_true, if_false, true_and, size_inner, size_leaf]
  all_goals try rfl
  all_goals try contradiction
  all_goals try (exfalso; tree_tac; done)
  all_goals congr; tree_tac

theorem balance_eq_balanceSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balance k v l r hlb hrb hlr = balanceSlow k v l r := by
  rw [balance.eq_def, balanceSlow.eq_def]
  repeat' (split; dsimp)
  all_goals try contradiction
  all_goals simp_all [-Nat.not_lt]

@[tree_tac]
theorem size_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balanceSlow k v l r).size = l.size + 1 + r.size :=
  (balanceSlow_desc hlb hrb hlr).1

@[tree_tac]
theorem balanced_balanceSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balanceSlow k v l r).Balanced :=
  (balanceSlow_desc hlb hrb hlr).2

@[tree_tac]
theorem size_balance {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balance_eq_balanceSlow, size_balanceSlow hlb hrb hlr]

@[tree_tac]
theorem balance_balance {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size ∨ BalanceLErasePrecond r.size l.size) :
    (balance k v l r hlb hrb hlr).Balanced := by
  rw [balance_eq_balanceSlow]
  exact balanced_balanceSlow hlb hrb hlr

@[tree_tac]
theorem size_balanceLSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLSlow k v l r).size = l.size + 1 + r.size := by
  rw [balanceLSlow_eq_balanceSlow hlb hrb hlr, size_balanceSlow hlb hrb (Or.inl hlr)]

@[tree_tac]
theorem balanced_balanceLSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLSlow k v l r).Balanced := by
  rw [balanceLSlow_eq_balanceSlow hlb hrb hlr]
  exact balanced_balanceSlow hlb hrb (Or.inl hlr)

@[tree_tac]
theorem size_balanceLErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLErase k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceLErase_eq_balanceLSlow, size_balanceLSlow hlb hrb hlr]

@[tree_tac]
theorem balanced_balanceLErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond l.size r.size) :
    (balanceLErase k v l r hlb hrb hlr).Balanced := by
  rw [balanceLErase_eq_balanceLSlow]
  exact balanced_balanceLSlow hlb hrb hlr

@[tree_tac]
theorem size_balanceL {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond l.size r.size) :
    (balanceL k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceL_eq_balanceLErase, size_balanceLErase]

@[tree_tac]
theorem balanced_balanceL {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond l.size r.size) :
    (balanceL k v l r hlb hrb hlr).Balanced := by
  rw [balanceL_eq_balanceLErase]
  exact balanced_balanceLErase hlb hrb hlr.erase

@[tree_tac]
theorem size_balanceRSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRSlow k v l r).size = l.size + 1 + r.size := by
  rw [balanceRSlow_eq_balanceSlow hlb hrb hlr, size_balanceSlow hlb hrb (Or.inr hlr)]

@[tree_tac]
theorem balanced_balanceRSlow {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRSlow k v l r).Balanced := by
  rw [balanceRSlow_eq_balanceSlow hlb hrb hlr]
  exact balanced_balanceSlow hlb hrb (Or.inr hlr)

@[tree_tac]
theorem size_balanceRErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRErase k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceRErase_eq_balanceRSlow, size_balanceRSlow hlb hrb hlr]

@[tree_tac]
theorem balanced_balanceRErase {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLErasePrecond r.size l.size) :
    (balanceRErase k v l r hlb hrb hlr).Balanced := by
  rw [balanceRErase_eq_balanceRSlow]
  exact balanced_balanceRSlow hlb hrb hlr

@[tree_tac]
theorem size_balanceR {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond r.size l.size) :
    (balanceR k v l r hlb hrb hlr).size = l.size + 1 + r.size := by
  rw [balanceR_eq_balanceRErase, size_balanceRErase]

@[tree_tac]
theorem balanced_balanceR {k : α} {v : β k} {l r : Impl α β} (hlb : l.Balanced) (hrb : r.Balanced)
    (hlr : BalanceLPrecond r.size l.size) :
    (balanceR k v l r hlb hrb hlr).Balanced := by
  rw [balanceR_eq_balanceRErase]
  exact balanced_balanceRErase hlb hrb hlr.erase

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
      let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := minView k' v' l' r' ✓ ✓ ✓
      ⟨dk, dv, ⟨balanceRErase k v dt r ✓ ✓ (by as_aux_lemma =>
        exact hlr.erase_left
          (by simp only [hdt', hl.eq, size_inner]; omega)
          (by simp only [hdt', hl.eq, size_inner]; omega)), ✓, ✓⟩⟩
  where triviality {n m : Nat} : n + 1 + m - 1 = n + m := by omega

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
      let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := maxView k' v' l' r' ✓ ✓ ✓
      ⟨dk, dv, ⟨balanceLErase k v l dt ✓ ✓ (by as_aux_lemma =>
        simp only [hdt', size_inner, hr.eq] at *
        apply hlr.erase_right <;> omega), ✓, ✓⟩⟩

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
  | .inner sz k v l' r' =>
    match r with
    | .leaf => l
    | .inner sz' k' v' l'' r'' =>
      if sz < sz' then
        let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := minView k' v' l'' r'' ✓ ✓ ✓
        balanceLErase dk dv (.inner sz k v l' r') dt hl ✓
          (by as_aux_lemma =>
            simp only [hdt', size_inner, hr.eq] at *
            apply hlr.erase_right <;> omega)
      else
        let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := maxView k v l' r' ✓ ✓ ✓
        balanceRErase dk dv dt (.inner sz' k' v' l'' r'') ✓ hr
          (by as_aux_lemma =>
            simp only [hdt', size_inner, hl.eq] at *
            apply hlr.erase_left <;> omega)

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
  | inner sz k' v' l' r' =>
      let ⟨l'', hl''₁, hl''₂⟩ := insertMin k v l' ✓
      ⟨balanceL k' v' l'' r' ✓ ✓ ✓, ✓, ✓⟩

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
  | inner sz k' v' l' r' =>
      let ⟨r'', hr''₁, hr''₂⟩ := insertMax k v r' ✓
      ⟨balanceR k' v' l' r'' ✓ ✓ ✓, ✓, ✓⟩

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

/-- Builds the tree `l ++ ⟨k, v⟩ ++ r` without any balancing information at the root. -/
def link (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) :
    Tree α β (l.size + 1 + r.size) :=
  match l with
  | leaf =>
      let d := insertMin k v r ✓
      ⟨d.impl, ✓, ✓⟩
  | (inner szl k' v' l' r') =>
      match r with
      | leaf =>
          let d := insertMax k v (inner szl k' v' l' r') ✓
          ⟨d.impl, ✓, ✓⟩
      | (inner szr k'' v'' l'' r'') =>
          if h₁ : delta * szl < szr then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link k v (inner szl k' v' l' r') l'' ✓ ✓
            ⟨balanceLErase k'' v'' ℓ r'' ✓ ✓ ✓, ✓, ✓⟩
          else if h₂ : delta * szr < szl then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link k v r' (inner szr k'' v'' l'' r'') ✓ ✓
            ⟨balanceRErase k' v' l' ℓ ✓ ✓ ✓, ✓, ✓⟩
          else
            ⟨.inner (szl + 1 + szr) k v (inner szl k' v' l' r') (inner szr k'' v'' l'' r''),
              ✓, ✓⟩
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

/-- Builds the tree `l ++ r` without any balancing information at the root. -/
def link2 (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) :
    Tree α β (l.size + r.size) :=
  match hl' : l with
  | leaf => ⟨r, ✓, ✓⟩
  | (inner szl k' v' l' r') =>
      match hr' : r with
      | leaf => ⟨l, ✓, ✓⟩
      | (inner szr k'' v'' l'' r'') =>
          if h₁ : delta * szl < szr then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link2 l l'' ✓ ✓
            ⟨balanceLErase k'' v'' ℓ r'' ✓ ✓ ✓, ✓, ✓⟩
          else if h₂ : delta * szr < szl then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link2 r' r ✓ ✓
            ⟨balanceRErase k' v' l' ℓ ✓ ✓ ✓, ✓, ✓⟩
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
structure TreeB (lb ub : Nat) where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced
  /-- The tree has size at least `lb`. -/
  lb_le_size_impl : lb ≤ impl.size
  /-- The tree has size at most `ub`. -/
  size_impl_le_ub : impl.size ≤ ub

attribute [tree_tac] TreeB.balanced_impl

/-- An empty tree. -/
@[inline]
def empty : Impl α β :=
  .leaf

@[tree_tac]
theorem balanced_empty : (empty : Impl α β).Balanced :=
  .leaf

attribute [tree_tac] or_true true_or

/-- Adds a new mapping to the key, overwriting an existing one with equal key if present. -/
def insert [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    TreeB α β l.size (l.size + 1) :=
  match l with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓, ✓⟩
  | inner sz k' v' l' r' =>
      match compare k k' with
      | .lt =>
          let ⟨d, hd, hd₁, hd₂⟩ := insert k v l' ✓
          ⟨balanceL k' v' d r' ✓ ✓ ✓, ✓, ✓, ✓⟩
      | .gt =>
          let ⟨d, hd, hd₁, hd₂⟩ := insert k v r' ✓
          ⟨balanceR k' v' l' d ✓ ✓ ✓, ✓, ✓, ✓⟩
      | .eq => ⟨.inner sz k v l' r', ✓, ✓, ✓⟩

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
    Bool × TreeB α β l.size (l.size + 1) :=
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
    TreeB α β l.size (l.size + 1) :=
  if l.contains k then ⟨l, ✓, ✓, ✓⟩ else l.insert k v ✓

/-- Slower version of `insertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `insertIfNew`, otherwise might panic. -/
@[inline]
def insertIfNewSlow [Ord α] (k : α) (v : β k) (l : Impl α β) :
    Impl α β :=
  if l.contains k then l else l.insertSlow k v

/-- Returns the pair `(l.contains k, l.insertIfNew k v)`. -/
@[inline]
def containsThenInsertIfNew [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Bool × TreeB α β l.size (l.size + 1) :=
  if l.contains k then (true, ⟨l, ✓, ✓, ✓⟩) else (false, l.insert k v ✓)

/-- Slower version of `containsThenInsertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `containsThenInsertIfNew`, otherwise might panic. -/
@[inline]
def containsThenInsertIfNewSlow [Ord α] (k : α) (v : β k) (l : Impl α β) :
    Bool × Impl α β :=
  if l.contains k then (true, l) else (false, l.insertSlow k v)

/-- Returns the pair `(l.get? k, l.insertIfNew k v)`. -/
@[inline]
def getThenInsertIfNew? [Ord α] [LawfulEqOrd α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Option (β k) × Impl α β :=
  match l.get? k with
  | some v' => (some v', l)
  | none => (none, (l.insertIfNew k v hl).impl)

/-- Slower version of `getThenInsertIfNew?` which can be used in the absence of balance
information but still assumes the preconditions of `getThenInsertIfNew?`, otherwise might panic. -/
@[inline]
def getThenInsertIfNewSlow? [Ord α] [LawfulEqOrd α] (k : α) (v : β k) (l : Impl α β) :
    Option (β k) × Impl α β :=
  match l.get? k with
  | some v' => (some v', l)
  | none => (none, l.insertIfNewSlow k v)

namespace Const

/-- Returns the pair `(l.get? k, l.insertIfNew k v)`. -/
@[inline]
def getThenInsertIfNew? [Ord α] (k : α) (v : δ) (l : Impl α (fun _ => δ)) (hl : l.Balanced) :
    Option δ × Impl α (fun _ => δ) :=
  match Const.get? k l with
  | some v' => (some v', l)
  | none => (none, (l.insertIfNew k v hl).impl)

/-- Slower version of `getThenInsertIfNew?` which can be used in the absence of balance
information but still assumes the preconditions of `getThenInsertIfNew?`, otherwise might panic. -/
@[inline]
def getThenInsertIfNewSlow? [Ord α] (k : α) (v : δ) (l : Impl α (fun _ => δ)) :
    Option δ × Impl α (fun _ => δ) :=
  match Const.get? k l with
  | some v' => (some v', l)
  | none => (none, l.insertIfNewSlow k v)

end Const

/-- Removes the mapping with key `k`, if it exists. -/
def erase [Ord α] (l : Impl α β) (k : α) (h : l.Balanced) : TreeB α β (l.size - 1) l.size :=
  match l with
  | leaf => ⟨.leaf, ✓, ✓, ✓⟩
  | inner sz k' v' l r =>
    match compare k k' with
    | .lt =>
      let ⟨l', hl'₁, hl'₂, hl'₃⟩ := erase l k ✓
      ⟨balanceRErase k' v' l' r ✓ ✓ ✓, ✓, ✓, ✓⟩
    | .gt =>
      let ⟨r', hr'₁, hr'₂, hr'₃⟩ := erase r k ✓
      ⟨balanceLErase k' v' l r' ✓ ✓ ✓, ✓, ✓, ✓⟩
    | .eq => ⟨glue l r ✓ ✓ ✓, ✓, ✓, ✓⟩

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
    | none =>
        let ⟨l', hl'⟩ := filterMap f l ✓
        let ⟨r', hr'⟩ := filterMap f r ✓
        ⟨(link2 l' r' ✓ ✓).impl, ✓⟩
    | some v' =>
        let ⟨l', hl'⟩ := filterMap f l ✓
        let ⟨r', hr'⟩ := filterMap f r ✓
        ⟨(link k v' l' r' ✓ ✓).impl, ✓⟩

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
    | false =>
        let ⟨l', hl'⟩ := filter f l ✓
        let ⟨r', hr'⟩ := filter f r ✓
        ⟨(link2 l' r'  ✓ ✓).impl, ✓⟩
    | true =>
        let ⟨l', hl'⟩ := filter f l ✓
        let ⟨r', hr'⟩ := filter f r ✓
        ⟨(link k v l' r' ✓ ✓).impl, ✓⟩

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

namespace Const

-- TODO: unify indentation

/-- Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it. -/
@[specialize]
def alter [Ord α] (k : α) (f : Option δ → Option δ) (l : Impl α (fun _ => δ)) (hl : l.Balanced) :
    TreeB α (fun _ => δ) (l.size - 1) (l.size + 1) :=
  match l with
  | .leaf =>
    match f none with
    | none => ⟨.leaf, ✓, ✓, ✓⟩
    | some v => ⟨.inner 1 k v .leaf .leaf, ✓, ✓, ✓⟩
  | .inner sz k' v' l' r' =>
    match compare k k' with
    | .lt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f l' ✓
        ⟨balance k' v' d r' ✓ ✓ (hl.at_root.adjust_left hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .gt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f r' ✓
        ⟨balance k' v' l' d ✓ ✓ (hl.at_root.adjust_right hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .eq =>
      match f (some v') with
      | none => ⟨glue l' r' ✓ ✓ ✓, ✓, ✓, ✓⟩
      | some v => ⟨.inner sz k' v l' r', ✓, ✓, ✓⟩

/-- Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic. -/
@[specialize]
def alterSlow [Ord α] (k : α) (f : Option δ → Option δ) (l : Impl α (fun _ => δ)) :
    Impl α (fun _ => δ) :=
  match l with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match compare k k' with
    | .lt => balanceSlow k' v' (alterSlow k f l') r'
    | .gt => balanceSlow k' v' l' (alterSlow k f r')
    | .eq =>
      match f (some v') with
      | none => glueSlow l' r'
      | some v => .inner sz k' v l' r'

end Const

/-- Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it.
This version of the function requires `LawfulEqOrd α`. There is an alternative non-dependent version
called `Const.modify`. -/
@[specialize]
def alter [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (l : Impl α β)
    (hl : l.Balanced) : TreeB α β (l.size - 1) (l.size + 1) :=
  match l with
  | .leaf =>
    match f none with
    | none => ⟨.leaf, ✓, ✓, ✓⟩
    | some v => ⟨.inner 1 k v .leaf .leaf, ✓, ✓, ✓⟩
  | .inner sz k' v' l' r' =>
    match h : compare k k' with
    | .lt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f l' ✓
        ⟨balance k' v' d r' ✓ ✓ (hl.at_root.adjust_left hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .gt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f r' ✓
        ⟨balance k' v' l' d ✓ ✓ (hl.at_root.adjust_right hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .eq =>
      match f (some (cast (congrArg β (eq_of_compare h).symm) v')) with
      | none => ⟨glue l' r' ✓ ✓ ✓, ✓, ✓, ✓⟩
      | some v => ⟨.inner sz k v l' r', ✓, ✓, ✓⟩

/-- Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic. -/
@[specialize]
def alterSlow [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (l : Impl α β) :
    Impl α β :=
  match l with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match h : compare k k' with
    | .lt => balanceSlow k' v' (alterSlow k f l') r'
    | .gt => balanceSlow k' v' l' (alterSlow k f r')
    | .eq =>
      match f (some (cast (congrArg β (eq_of_compare h).symm) v')) with
      | none => glueSlow l' r'
      | some v => .inner sz k v l' r'

/-- If the tree contains a mapping `(k', v)` with `k == k'`, adjust it to have mapping
`(k', f k' v h)`, which `h : compare k k' = .eq`. If no such mapping is present, returns the
tree unmodified. Note that this function is likely to be faster than `modify` because it never
needs to rebalance the tree. -/
def modify [Ord α] (k : α) (f : (k' : α) → β k' → (compare k k' = .eq) → β k') (l : Impl α β) :
    Impl α β :=
  match l with
  | .leaf => .leaf
  | .inner sz k' v' l r =>
    match h : compare k k' with
    | .lt => .inner sz k' v' (modify k f l) r
    | .gt => .inner sz k' v' l (modify k f r)
    | .eq => .inner sz k' (f k' v' h) l r

attribute [tree_tac] Nat.compare_eq_gt Nat.compare_eq_lt Nat.compare_eq_eq

/-- Returns the mapping with the `n`-th smallest key. -/
def atIndex [Ord α] : (l : Impl α β) → (hl : l.Balanced) → (n : Nat) → (h : n < l.size) → (a : α) × β a
  | .inner _ k v l' r', hl, n, h =>
    match h : compare n l'.size with
    | .lt => l'.atIndex hl.left n ✓
    | .eq => ⟨k, v⟩
    | .gt => r'.atIndex hl.right (n - l'.size - 1) ✓

/-- Folds the given function over the mappings in the tree in ascending order. -/
@[specialize]
def foldlM [Monad m] (f : δ → (a : α) → β a → m δ) (init : δ) : Impl α β → m δ
  | .leaf => pure init
  | .inner _ k v l r => do
    let left ← foldlM f init l
    let middle ← f left k v
    foldlM f middle r

/-- Folds the given function over the mappings in the tree in ascending order. -/
@[inline]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (l : Impl α β) : δ :=
  Id.run (l.foldlM f init)

/-- Applies the given function to the mappings in the tree in ascending order. -/
@[inline]
def forM [Monad m] (f : (a : α) → β a → m PUnit) (l : Impl α β) : m PUnit :=
  l.foldlM (fun _ k v => f k v) ⟨⟩

/-- Implementation detail. -/
@[specialize]
def forInStep [Monad m] (f : δ → (a : α) → β a → m (ForInStep δ)) (init : δ) :
    Impl α β → m (ForInStep δ)
  | .leaf => pure (.yield init)
  | .inner _ k v l r => do
    match ← forInStep f init l with
    | ForInStep.done d => return (.done d)
    | ForInStep.yield d =>
      match ← f d k v with
      | ForInStep.done d => return (.done d)
      | ForInStep.yield d => forInStep f d r

/-- Support for the `for` construct in `do` blocks. -/
@[inline]
def forIn [Monad m] (f : δ → (a : α) → β a → m (ForInStep δ)) (init : δ) (l : Impl α β) : m δ := do
  match ← forInStep f init l with
  | ForInStep.done d => return d
  | ForInStep.yield d => return d

/-- Flattens a tree into a list of key-value pairs. This function is defined for verification
purposes and should not be executed because it is very inefficient. -/
def toListModel : Impl α β → List ((a : α) × β a)
  | .leaf => []
  | .inner _ k v l r => l.toListModel ++ ⟨k, v⟩ :: r.toListModel

/-- The binary search tree property. -/
def Ordered [Ord α] (l : Impl α β) : Prop :=
  l.toListModel.Pairwise (fun a b => compare a.1 b.1 = .lt)

/-- Well-formedness of ordered trees. -/
inductive WF [Ord α] : Impl α β → Prop where
  /-- This is the actual well-formedness invariant: the tree must be a balanced BST. -/
  | wf {l} : Balanced l → (∀ [TransOrd α], Ordered l) → WF l
  /-- The empty tree is well-formed. Later shown to be subsumed by `.wf`. -/
  | empty : WF .empty
  /-- `insert` preserves well-formedness. Later shown to be subsumed by `.wf`. -/
  | insert {l h k v} : WF l → WF (l.insert k v h).impl

set_option debug.byAsSorry false

/-- A well-formed tree is balanced. This is needed here already because we need to know that the
tree is balanced to call the optimized modification functions. -/
theorem WF.balanced [Ord α] {l : Impl α β} : WF l → l.Balanced
  | .wf h _ => h
  | .empty => balanced_empty
  | .insert _ => TreeB.balanced_impl _

end Impl

end Std.DOrderedTree.Internal

-- open Lean

-- run_meta do
--   let env ← getEnv
--   let mut arr : Array (Nat × Name × MessageData) := #[]
--   let mut unknown : Array Name := #[]
--   let mut totalSize : Nat := 0
--   for (name, info) in env.constants do
--     if (`Std.DOrderedTree.Internal.Impl).isPrefixOf name then
--       if let some e := info.value? then
--         let numObjs ← e.numObjs
--         arr := arr.push (numObjs, (name, m!"{info.type}"))
--         totalSize := totalSize + numObjs
--       else
--         unknown := unknown.push name
--   arr := arr.qsort (fun a b => a.1 > b.1)
--   logInfo m!"total size: {totalSize}"
--   for (a, (b, c)) in arr do
--     logInfo m!"({a}, {b}, {c})"
