/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Lemmas
import Orderedtree.DOrderedTree.Basic

/-!
# API lemmas for `DOrderedTree`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DOrderedTree.Internal

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}

namespace Std.DOrderedTree

theorem contains_insert [h : TransCmp cmp] (m : DOrderedTree α β cmp) {k a : α} {v : β k} :
    (m.insert k v).contains a = (cmp k a == .eq || m.contains a) :=
  let _ : Ord α := ⟨cmp⟩
  have : OrientedOrd α := ⟨⟩
  have : TransOrd α := ⟨h.le_trans⟩
  Impl.contains_insert m.inner m.wf

end Std.DOrderedTree
