/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.OrderedTree.Basic

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

structure OrderedSet (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the binary search tree. -/
  inner : OrderedTree α Unit cmp

namespace OrderedSet

@[inline]
def empty : OrderedSet α cmp :=
  ⟨OrderedTree.empty⟩

@[inline]
def isEmpty (t : OrderedSet α cmp) : Bool :=
  t.inner.isEmpty

@[inline]
def insert (l : OrderedSet α cmp) (a : α) : OrderedSet α cmp :=
  ⟨l.inner.insert a ()⟩

@[inline]
def contains (l : OrderedSet α cmp) (a : α) : Bool :=
  l.inner.contains a

end OrderedSet

end Std
