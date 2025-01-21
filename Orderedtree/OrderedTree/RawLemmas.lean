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

namespace Std.OrderedTree.Raw

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : OrderedTree.Raw α β cmp}

attribute [local instance] TransOrd.ofTransCmp

theorem isEmpty_empty : (empty : OrderedTree.Raw α β cmp).isEmpty :=
  DOrderedTree.Raw.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DOrderedTree.Raw.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  DOrderedTree.Raw.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  DOrderedTree.Raw.mem_congr h hab

theorem contains_empty {k : α} : (empty : OrderedTree.Raw α β cmp).contains k = false :=
  DOrderedTree.Raw.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : OrderedTree.Raw α β cmp) :=
  DOrderedTree.Raw.mem_empty

theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DOrderedTree.Raw.contains_insert h

end Std.OrderedTree.Raw
