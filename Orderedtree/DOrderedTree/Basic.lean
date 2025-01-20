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

/-- Binary search trees. -/
structure DOrderedTree (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the binary search tree. -/
  inner : DOrderedTree.Internal.Impl α β
  /-- Internal implementation detail of the binary search tree. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DOrderedTree

@[inline]
def isEmpty (t : DOrderedTree α β cmp) : Bool :=
  t.inner.isEmpty

/-- Creates a new empty binary search tree. -/
@[inline]
def empty : DOrderedTree α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

/-- Inserts the mapping `(a, b)` into the binary search tree. -/
@[inline]
def insert (l : DOrderedTree α β cmp) (a : α) (b : β a) : DOrderedTree α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.insert a b l.wf.balanced).impl, .insert l.wf⟩

/-- Returns `true` if the given key is present in the map. -/
@[inline]
def contains (l : DOrderedTree α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; l.inner.contains a

end DOrderedTree

end Std
