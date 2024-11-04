/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Raw

open Std

def inversions (l : List Nat) : Nat := Id.run do
  let mut m : DOrderedTree.Raw Nat (fun _ => Unit) := .leaf
  let mut ans := 0
  for x in l do
    let insPt : Nat := m.insertionPoint x
    ans := ans + (m.size - insPt)
    m := DOrderedTree.Raw.insert x () ⟨m, sorry⟩
  return ans

def ofList (l : List (Nat × Nat)) : DOrderedTree.Raw Nat (fun _ => Nat) :=
  l.foldl (init := .leaf) (fun l (a, b) => DOrderedTree.Raw.insert a b ⟨l, sorry⟩)

#eval! inversions [4, 3, 1, 2]
