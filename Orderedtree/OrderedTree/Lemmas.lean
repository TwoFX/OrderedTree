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

namespace Std.OrderedTree

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : OrderedTree α β cmp}

theorem isEmpty_empty : (empty : OrderedTree α β cmp).isEmpty :=
  DOrderedTree.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  DOrderedTree.mem_iff_contains

theorem contains_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  DOrderedTree.contains_congr hab

theorem mem_congr [TransCmp cmp] {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  DOrderedTree.mem_congr hab

theorem contains_empty {k : α} : (empty : OrderedTree α β cmp).contains k = false :=
  DOrderedTree.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : OrderedTree α β cmp) :=
  DOrderedTree.mem_empty

theorem contains_insert [h : TransCmp cmp] {k a : α} {v : β} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  DOrderedTree.contains_insert

end Std.OrderedTree
