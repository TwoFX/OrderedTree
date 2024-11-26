/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Basic

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

@[inherit_doc DOrderedTree]
structure OrderedTree (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the binary search tree. -/
  inner : DOrderedTree α (fun _ => β) cmp

namespace OrderedTree

@[inline, inherit_doc DOrderedTree.empty]
def empty : OrderedTree α β cmp :=
  ⟨DOrderedTree.empty⟩

@[inline, inherit_doc DOrderedTree.insert]
def insert (l : OrderedTree α β cmp) (a : α) (b : β) : OrderedTree α β cmp :=
  ⟨l.inner.insert a b⟩

@[inline, inherit_doc DOrderedTree.contains]
def contains (l : OrderedTree α β cmp) (a : α) : Bool :=
  l.inner.contains a

end OrderedTree

end Std
