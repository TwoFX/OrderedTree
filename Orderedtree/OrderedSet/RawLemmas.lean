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

namespace Std.OrderedSet.Raw

attribute [local instance] TransOrd.ofTransCmp

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : OrderedSet.Raw α cmp}

theorem isEmpty_empty : (empty : OrderedSet.Raw α cmp).isEmpty :=
  OrderedTree.Raw.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  OrderedTree.Raw.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  OrderedTree.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  OrderedTree.Raw.mem_congr h hab

theorem contains_empty {k : α} : (empty : OrderedSet.Raw α cmp).contains k = false :=
  OrderedTree.Raw.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : OrderedSet.Raw α cmp) :=
  OrderedTree.Raw.mem_empty

theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  OrderedTree.Raw.contains_insert h

end Std.OrderedSet.Raw
