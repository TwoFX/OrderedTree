/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.List.Associative

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

-- TODO: this doesn't really gain you anything over defining it to be `k ∈ keys l.toList`.
inductive Mem (k : α) : Raw α β → Prop
  | node {s v l r} : Mem k (Raw.inner s k v l r)
  | left {s k' v l r} : Mem k l → Mem k (Raw.inner s k' v l r)
  | right {s k' v l r} : Mem k r → Mem k (Raw.inner s k' v l r)

instance : Membership α (Raw α β) where
  mem l k := Mem k l

@[simp]
theorem not_mem_leaf {k : α} : ¬k ∈ (Raw.leaf : Raw α β) := by
  rintro (_|_|_)

@[simp]
theorem mem_inner_iff {k : α} {s k' v l r} :
    k ∈ (Raw.inner s k' v l r : Raw α β) ↔ k ∈ l ∨ k = k' ∨ k ∈ r := by
  refine ⟨?_, ?_⟩
  · rintro (_|h|h)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h|rfl|h)
    · exact Mem.left h
    · exact Mem.node
    · exact Mem.right h

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

@[simp]
theorem ordered_inner_leaf_leaf [Ord α] {s k v} : (Raw.inner s k v .leaf .leaf : Raw α β).Ordered := by
  apply Ordered.inner <;> simp

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


@[specialize] def insert [Ord α] (k : α) (v : β k) : Raw α β → Raw α β
| leaf => .inner 1 k v .leaf .leaf
| inner sz ky y l r =>
  match compare k ky with
  | .lt => balanceL ky y (insert k v l) r sorry sorry sorry
  | .eq => .inner sz k v l r
  | .gt => balanceR ky y l (insert k v r) sorry sorry

def insertWithoutRebalancing [Ord α] (k : α) (v : β k) : Raw α β → Raw α β
| leaf => .inner 1 k v .leaf .leaf
| inner sz ky y l r =>
  match compare k ky with
  | .lt => .inner (sz + 1) ky y (insertWithoutRebalancing k v l) r
  | .eq => .inner sz k v l r
  | .gt => .inner (sz + 1) ky y l (insertWithoutRebalancing k v r)

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
           | none => sorry -- delete
           | some ⟨ky', y'⟩ => .inner sz ky' y' l r
  | .gt =>
      let newR := updateAtKey k f r
      .inner (1 + l.size + newR.size) ky y l newR

def insertₘ [Ord α] (k : α) (v : β k) : Raw α β → Raw α β :=
  updateAtKey k (fun _ => some ⟨k, v⟩)

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

def depth : Raw α β → Nat
| leaf => 0
| inner _ _ _ l r => 1 + max l.depth r.depth

def toList : Raw α β → List ((a : α) × β a)
| leaf => []
| inner _ k v l r => l.toList ++ ⟨k, v⟩ :: r.toList

@[simp]
theorem toList_leaf : (Raw.leaf : Raw α β).toList = [] := rfl

@[simp]
theorem toList_inner {s k v l r} :
    (Raw.inner s k v l r : Raw α β).toList = l.toList ++ ⟨k, v⟩ :: r.toList := rfl



theorem toList_balanceR (k : α) (v : β k) (l r : Raw α β) (h₁ h₂) : (balanceR k v l r h₁ h₂).toList = (Raw.inner 0 k v l r).toList :=
  sorry

theorem toList_balanceL (k : α) (v : β k) (l r : Raw α β) (h₁ h₂ h₃) : (balanceL k v l r h₁ h₂ h₃).toList = (Raw.inner 0 k v l r).toList :=
  sorry

theorem toList_insert_eq_toList_insertWithoutRebalancing [Ord α] {l : Raw α β} {k : α} {v : β k} :
    (l.insert k v).toList = (l.insertWithoutRebalancing k v).toList := by
  apply Raw.insert.induct k v (motive := fun l => (l.insert k v).toList = (l.insertWithoutRebalancing k v).toList)
  · simp [insert, insertWithoutRebalancing]
  all_goals
    intros
    simp_all [insert, insertWithoutRebalancing, toList_balanceL, toList_balanceR]

theorem toList_insertWithoutRebalancing_eq_toList_insertₘ [Ord α] {l : Raw α β} {k : α} {v : β k} :
    (l.insertWithoutRebalancing k v).toList = (l.insertₘ k v).toList := by
  induction l using Raw.insertWithoutRebalancing.induct k v
    <;> simp_all [insertWithoutRebalancing, insertₘ, updateAtKey]


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

theorem beq_of_mem_getEntry [Ord α] [TransOrd α] {l : Raw α β} {k : α} {p} : p ∈ l.getEntry? k → k == p.1 := by
  induction l using Raw.getEntry?.induct k
  · simp [getEntry?]
  · simp_all [getEntry?]
  · simp_all [getEntry?]
  · simp_all [getEntry?]
    rintro rfl
    exact beq_iff.2 (by simpa)

theorem Ordered.distinctKeys [Ord α] [TransOrd α] {l : Raw α β} (h : l.Ordered) : DistinctKeys l.toList := by
  induction h
  · simp
  · next s k v l r h₁ h₂ h₃ h₄ h₅ h₆ =>
    rw [toList, distinctKeys_append, distinctKeys_cons_iff]
    refine ⟨h₅, ⟨h₆, ?_⟩, ?_⟩
    · rw [containsKey_eq_false_iff_forall_mem_keys]
      simp only [mem_keys_toList]
      intro k' hk'
      exact beq_eq_false_of_lt (h₄ _ hk')
    · simp only [mem_keys_toList, keys_cons, List.mem_cons, forall_eq_or_imp]
      refine fun k' hk' => ⟨beq_eq_false_of_lt (h₃ _ hk'), fun k'' hk'' => ?_⟩
      exact beq_eq_false_of_lt (lt_trans (h₃ _ hk') (h₄ _ hk''))

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
  · sorry -- delete case
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
  · -- erase case
    sorry
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
  · sorry -- erase case
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

theorem exists_cell [Ord α] (l : Raw α β) (k : α) : ∃ (l' : List ((a : α) × β a)),
    l.toList.Perm ((l.getEntry? k).toList ++ l') ∧
    (∀ [TransOrd α], l.Ordered → containsKey k l' = false) := by
  obtain ⟨l', h₁, -, h₂⟩ := exists_cell_of_update l k id
  exact ⟨l', h₁, h₂⟩

theorem toList_insert [Ord α] [TransOrd α] (l : Raw α β) (k : α) (v : β k) (h : l.Ordered) :
    List.Perm (toList (l.insert k v)) (insertEntry k v l.toList) := by
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

end Raw

end DOrderedTree

end Std
