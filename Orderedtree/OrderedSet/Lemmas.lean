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

namespace Std.OrderedSet

variable {α : Type u} {cmp : α → α → Ordering} {t : OrderedSet α cmp}

theorem isEmpty_empty : (empty : OrderedSet α cmp).isEmpty :=
  OrderedTree.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  OrderedTree.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  OrderedTree.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  OrderedTree.mem_congr hab

theorem contains_empty {k : α} : (empty : OrderedSet α cmp).contains k = false :=
  OrderedTree.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : OrderedSet α cmp) :=
  OrderedTree.mem_empty

theorem contains_insert [h : TransCmp cmp] (t : OrderedSet α cmp) {k a : α} :
    (t.insert k).contains a = (cmp k a == .eq || t.contains a) :=
  OrderedTree.contains_insert

end Std.OrderedSet
