/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Impl
import Lean.Data.RBMap

open Std.DOrderedTree.Internal

abbrev α : Type := Nat
abbrev β : α → Type := fun _ => Nat

macro "bench" typ:term "ee" empty:term "ee" func:term " ee " out:ident "ee" msg:term : command => `(
  @[noinline] def run (values : Array α) : Nat × $typ := Id.run do
    let mut cnt := 0
    let mut m := $empty
    for v in values do
      let (c, m') := $func v v m sorry
      m := m'.1
      if c then cnt := 1
    return (cnt, m)

  def run' (values : Array α) : IO (Nat × $typ) := do
    return run values

  def $out (values : Array α) : IO Unit := do
    IO.println $msg
    for _ in [:20] do
      let _ ← timeit "" $ run' values
)

@[inline]
def leanContainsThenInsert (k : Nat) (v : Nat) (l : Lean.RBMap Nat Nat Ord.compare) (_h : True) :
    (Bool × { _m : Lean.RBMap Nat Nat Ord.compare // True }) :=
  (l.contains k, ⟨l.insert k v, trivial⟩)

bench (Impl α β) ee Impl.empty ee Impl.containsThenInsert₁ ee bench₁ ee "First"
bench (Impl α β) ee Impl.empty ee Impl.containsThenInsert₂ ee bench₂ ee "Second"
bench (Impl α β) ee Impl.empty ee Impl.containsThenInsert₃ ee bench₃ ee "Third"
bench (Lean.RBMap Nat Nat Ord.compare) ee Lean.RBMap.empty ee leanContainsThenInsert ee bench₄ ee "Fourth"

def n : Nat := 100000

def mkArr : Array α :=
  Array.range (2 * n) ++ (Array.range n |>.map (·*2))

def main : IO Unit := do
  let values := mkArr
  bench₁ values
  bench₂ values
  bench₃ values
  bench₄ values
  bench₁ values
  bench₂ values
  bench₃ values
  bench₄ values
