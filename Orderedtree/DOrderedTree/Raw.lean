/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
universe u v

variable {α : Type u} {β : α → Type v}

inductive TreeNode (α : Type u) (β : α → Type v) where
  | inner (size : Nat) (k : α) (v : β k) (l r : TreeNode α β)
  | leaf

namespace TreeNode

@[inline]
def delta : Nat := 3
@[inline]
def ratio : Nat := 2

@[inline]
def size : TreeNode α β → Nat
  | inner s _ _ _ _ => s
  | leaf => 0

instance : Inhabited (TreeNode α β) where
  default := .leaf


@[inline] def balanceL (k : α) (v : β k) (l r : TreeNode α β) : TreeNode α β :=
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
  | r@(inner rs _ _ _ _) => match l with
    | leaf => .inner (1 + rs) k v .leaf r
    | l@(inner ls lk lv ll lr) =>
        if ls > delta * rs then match ll, lr with
          | inner lls _ _ _ _, inner lrs lrk lrv lrl lrr =>
              if lrs < ratio * lls then .inner (1 + ls + rs) lk lv ll (.inner (1 + rs + lrs) k v lr r)
              else .inner (1 + ls + rs) lrk lrv (.inner (1 + lls + lrl.size) lk lv ll lrl) (.inner (1 + rs + lrr.size) k v lrr r)
          | _, _ => False.elim sorry
        else .inner (1 + ls + rs) k v l r

@[inline] def balanceR (k : α) (v : β k) (l r : TreeNode α β) : TreeNode α β :=
  match l with
  | leaf => match r with
    | leaf => .inner 1 k v .leaf .leaf
    | r@(inner _ _ _ .leaf .leaf) => .inner 2 k v .leaf r
    | inner _ rk rv .leaf rr@(.inner _ _ _ _ _) => .inner 3 rk rv (.inner 1 k v .leaf .leaf) rr
    | inner _ rk rv (.inner _ rlk rlv _ _) .leaf => .inner 3 rlk rlv (.inner 1 k v .leaf .leaf) (.inner 1 rk rv .leaf .leaf)
    | inner rs rk rv rl@(.inner rls rlk rlv rll rlr) rr@(.inner rrs _ _ _ _) =>
        if rls < ratio * rrs then .inner (1 + rs) rk rv (.inner (1 + rls) k v .leaf rl) rr
        else .inner (1 + rs) rlk rlv (.inner (1 + rll.size) k v .leaf rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
  | l@(inner ls _ _ _ _) => match r with
    | leaf => .inner (1 + ls) k v l .leaf
    | r@(inner rs rk rv rl rr) =>
        if rs > delta * ls then match rl, rr with
          | inner rls rlk rlv rll rlr, .inner rrs _ _ _ _ =>
              if rls < ratio * rrs then .inner (1 + ls + rs) rk rv (.inner (1 + ls + rls) k v l rl) rr
              else .inner (1 + ls + rs) rlk rlv (.inner (1 + ls + rll.size) k v l rll) (.inner (1 + rrs + rlr.size) rk rv rlr rr)
          | _, _ => False.elim sorry
        else .inner (1 + ls + rs) k v l r


@[specialize] def insert (cmp : α → α → Ordering) (k : α) (v : β k) : TreeNode α β → TreeNode α β
| leaf => .inner 1 k v .leaf .leaf
| inner sz ky y l r => match cmp k ky with
    | .lt => balanceL ky y (insert cmp k v l) r
    | .eq => .inner sz k v l r
    | .gt => balanceR ky y l (insert cmp k v r)

@[specialize] def find (cmp : α → α → Ordering) (h : ∀ {k₁ k₂}, cmp k₁ k₂ = .eq → k₁ = k₂) (k : α) : TreeNode α β → Option (β k)
| leaf => none
| inner _ ky y l r =>
    match hc : cmp k ky with
    | .lt => find cmp h k l
    | .gt => find cmp h k r
    | .eq => some (cast (congrArg β (h hc).symm) y)

@[specialize] def insertionPoint (cmp : α → α → Ordering) (k : α) (t : TreeNode α β) : Nat :=
  go 0 t
where
  @[specialize] go (sofar : Nat) : TreeNode α β → Nat
  | leaf => sofar
  | inner _ ky _ l r =>
    match cmp k ky with
    | .lt => go sofar l
    | .eq => sofar + size l
    | .gt => go (sofar + 1 + size l) r

def inversions (l : List Nat) : Nat := Id.run do
  let mut m : TreeNode Nat (fun _ => Unit) := .leaf
  let mut ans := 0
  for x in l do
    let insPt : Nat := insertionPoint Ord.compare x m
    ans := ans + (m.size - insPt)
    m := m.insert Ord.compare x ()
  return ans

#eval! inversions [6,5,4,3,2,7,1]

def depth : TreeNode α β → Nat
| leaf => 0
| inner _ _ _ l r => 1 + max l.depth r.depth

end TreeNode
