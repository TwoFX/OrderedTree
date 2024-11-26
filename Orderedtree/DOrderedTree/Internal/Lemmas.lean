/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.WF

/-!
# API lemmas for `DOrderedTree.Impl`
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DHashMap.Internal
open Std.DHashMap.Internal.List

universe u v

variable {α : Type u} {β : α → Type v}

namespace Std.DOrderedTree.Internal.Impl

/-- Internal implementation detail of the hash map -/
scoped macro "wf_trivial" : tactic => `(tactic|
  repeat (first
    | apply WF.ordered | apply WF.balanced | apply WF.insert | apply WF.insertSlow | assumption
    ))

/-- Internal implementation detail of the hash map -/
scoped macro "empty" : tactic => `(tactic| { intros; simp_all [List.isEmpty_iff] } )

open Lean

private def queryNames : Array Name :=
  #[``apply_contains]

private def modifyNames : Array Name :=
  #[``toListModel_insert, ``toListModel_insertSlow]

private def congrNames : MacroM (Array (TSyntax `term)) := do
  return #[← `(_root_.List.Perm.isEmpty_eq), ← `(containsKey_of_perm),
    ← `(_root_.List.Perm.length_eq), ← `(getValueCast?_of_perm _),
    ← `(getValue?_of_perm _), ← `(getValue_of_perm _), ← `(getValueCast_of_perm _),
    ← `(getValueCast!_of_perm _), ← `(getValueCastD_of_perm _), ← `(getValue!_of_perm _),
    ← `(getValueD_of_perm _), ← `(getKey?_of_perm _), ← `(getKey_of_perm _), ← `(getKeyD_of_perm _),
    ← `(getKey!_of_perm _)]

/-- Internal implementation detail of the hash map -/
scoped syntax "simp_to_model" ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[using $using?]?) => do
  let mut congrModify : Array (TSyntax `term) := #[]
  for congr in (← congrNames) do
    for modify in modifyNames do
      congrModify := congrModify.push (← `($congr:term ($(mkIdent modify) ..)))
  `(tactic|
    (simp (discharger := wf_trivial) only
      [$[$(Array.map Lean.mkIdent queryNames):term],*, $[$congrModify:term],*]
     $[apply $(using?.toArray):term];*)
    <;> wf_trivial)

attribute [local instance] beqOfOrd
attribute [local instance] equivBEq_of_transOrd

theorem contains_insert [Ord α] [TransOrd α] (m : Impl α β) (h : m.WF) {k a : α} {v : β k} :
    (m.insert k v h.balanced).impl.contains a = (compare k a == .eq || m.contains a) := by
  simp_to_model using List.containsKey_insertEntry

theorem contains_insertSlow [Ord α] [TransOrd α] (m : Impl α β) (h : m.WF) {k a : α} {v : β k} :
    (m.insertSlow k v).contains a = (compare k a == .eq || m.contains a) := by
  simp_to_model using List.containsKey_insertEntry

end Std.DOrderedTree.Internal.Impl
