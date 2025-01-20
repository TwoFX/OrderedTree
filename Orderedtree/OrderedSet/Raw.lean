/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.OrderedTree.Raw

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

namespace OrderedSet

structure Raw (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the binary search tree. -/
  inner : OrderedTree.Raw α Unit cmp

namespace Raw

structure WF (l : Raw α cmp) where
  /-- Internal implementation detail of the binary search tree. -/
  out : l.inner.WF

@[inline]
def empty : Raw α cmp :=
  ⟨OrderedTree.Raw.empty⟩

@[inline]
def isEmpty (t : Raw α cmp) : Bool :=
  t.inner.isEmpty

@[inline]
def insert (l : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨l.inner.insert a ()⟩

@[inline]
def insertFast (l : Raw α cmp) (h : l.WF) (a : α) : Raw α cmp :=
  ⟨l.inner.insertFast h.out a ()⟩

@[inline]
def contains (l : Raw α cmp) (a : α) : Bool :=
  l.inner.contains a

end Raw

end OrderedSet

end Std
