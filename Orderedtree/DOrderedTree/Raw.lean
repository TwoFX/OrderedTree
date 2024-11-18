/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Impl

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}

namespace Std

namespace DOrderedTree

/-- Binary search trees without a well-formedness invariant, suitable for use in nested inductive
types. -/
structure Raw (α : Type u) (β : α → Type v) (_cmp : α → α → Ordering) where
  /-- Internal implementation detail of the binary search tree. -/
  inner : Internal.Impl α β

namespace Raw

/-- Unbundled well-formedness invariant for `Raw α β cmp`. -/
structure WF (l : Raw α β cmp) where
  /-- Internal implementation detail of the binary search tree. -/
  out : letI : Ord α := ⟨cmp⟩; l.inner.WF

/-- Creates a new empty binary search tree. -/
@[inline]
def empty : Raw α β cmp :=
  ⟨Internal.Impl.empty⟩

/-- Inserts the mapping `(a, b)` into the binary search tree. -/
@[inline]
def insert (l : Raw α β cmp) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨l.inner.insertSlow a b⟩

/-- Inserts the mapping `(a, b)` into the binary search tree, but faster! -/
@[inline]
def insertFast (l : Raw α β cmp) (h : l.WF) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.insert a b h.out.balanced).impl⟩

/-- Returns `true` if the given key is present in the map. -/
@[inline]
def contains (l : Raw α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; l.inner.contains a

end Raw

end DOrderedTree

end Std
