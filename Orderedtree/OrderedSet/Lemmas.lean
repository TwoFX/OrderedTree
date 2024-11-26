/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.OrderedTree.Lemmas
import Orderedtree.OrderedSet.Basic

/-!
# API lemmas for `OrderedTree`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DOrderedTree.Internal

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std.OrderedSet

theorem contains_insert [h : TransCmp cmp] (m : OrderedSet α cmp) {k a : α} :
    (m.insert k).contains a = (cmp k a == .eq || m.contains a) :=
  OrderedTree.contains_insert m.inner

end Std.OrderedSet
