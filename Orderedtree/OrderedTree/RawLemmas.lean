/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.RawLemmas
import Orderedtree.OrderedTree.Raw

/-!
# API lemmas for `OrderedTree.Raw`
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std.OrderedTree.Raw

theorem isEmpty_empty : (empty : OrderedTree.Raw α β cmp).isEmpty :=
  DOrderedTree.Raw.isEmpty_empty

theorem contains_insert [h : TransCmp cmp] (m : OrderedTree.Raw α β cmp) (hm : m.WF) {k a : α} {v : β} :
    (m.insert k v).contains a = (cmp k a == .eq || m.contains a) :=
  DOrderedTree.Raw.contains_insert _ hm.out

end Std.OrderedTree.Raw
