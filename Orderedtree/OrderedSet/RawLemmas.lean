/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.OrderedTree.RawLemmas
import Orderedtree.OrderedSet.Raw

/-!
# API lemmas for `OrderedTree.Raw`
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std.OrderedSet.Raw

theorem isEmpty_empty : (empty : OrderedSet.Raw α cmp).isEmpty :=
  OrderedTree.Raw.isEmpty_empty

theorem contains_insert [h : TransCmp cmp] (m : OrderedSet.Raw α cmp) (hm : m.WF) {k a : α} :
    (m.insert k).contains a = (cmp k a == .eq || m.contains a) :=
  OrderedTree.Raw.contains_insert _ hm.out

end Std.OrderedSet.Raw
