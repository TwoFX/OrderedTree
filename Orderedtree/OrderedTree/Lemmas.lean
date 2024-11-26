/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Lemmas
import Orderedtree.OrderedTree.Basic

/-!
# API lemmas for `OrderedTree`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DOrderedTree.Internal

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std.OrderedTree

theorem contains_insert [h : TransCmp cmp] (m : OrderedTree α β cmp) {k a : α} {v : β} :
    (m.insert k v).contains a = (cmp k a == .eq || m.contains a) :=
  DOrderedTree.contains_insert m.inner

end Std.OrderedTree
