/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Raw

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

namespace OrderedTree

@[inherit_doc DOrderedTree.Raw]
structure Raw (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the binary search tree. -/
  inner : DOrderedTree.Raw α (fun _ => β) cmp

namespace Raw

@[inherit_doc DOrderedTree.Raw.WF]
structure WF (l : Raw α β cmp) where
  /-- Internal implementation detail of the binary search tree. -/
  out : l.inner.WF

instance {t : Raw α β cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

@[inline, inherit_doc DOrderedTree.Raw.empty]
def empty : Raw α β cmp :=
  ⟨DOrderedTree.Raw.empty⟩

@[inline, inherit_doc DOrderedTree.Raw.isEmpty]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DOrderedTree.Raw.insert]
def insert (l : Raw α β cmp) (a : α) (b : β) : Raw α β cmp :=
  ⟨l.inner.insert a b⟩

@[inline, inherit_doc DOrderedTree.Raw.insertFast]
def insertFast (l : Raw α β cmp) (h : l.WF) (a : α) (b : β) : Raw α β cmp :=
  ⟨l.inner.insertFast h.out a b⟩

@[inline, inherit_doc DOrderedTree.Raw.contains]
def contains (l : Raw α β cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (Raw α β cmp) where
  mem m a := m.contains a

end Raw

end OrderedTree

end Std
