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
    let insPt : Nat := m.insertionPoint Ord.compare x
    ans := ans + (m.size - insPt)
    m := m.insert Ord.compare x ()
  return ans
