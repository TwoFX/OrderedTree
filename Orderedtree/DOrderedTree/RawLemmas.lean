/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Lemmas
import Orderedtree.DOrderedTree.Raw

/-!
# API lemmas for `DOrderedTree.Raw`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DOrderedTree.Internal

universe u v

namespace Std.DOrderedTree.Raw

attribute [local instance] TransOrd.ofTransCmp

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : DOrderedTree.Raw α β cmp}

theorem isEmpty_empty : (empty : DOrderedTree.Raw α β cmp).isEmpty :=
  Impl.isEmpty_empty

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' == .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr h hab

theorem contains_empty {k : α} : (empty : DOrderedTree.Raw α β cmp).contains k = false :=
  Impl.contains_empty

theorem mem_empty {k : α} : k ∉ (empty : DOrderedTree.Raw α β cmp) :=
  Impl.mem_empty

theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insertSlow h

end Std.DOrderedTree.Raw
