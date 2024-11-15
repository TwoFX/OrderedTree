/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Impl
import Lean.Data.RBMap

namespace Bench.InsertIfNew

open Std.DOrderedTree.Internal Impl

partial def fisherYates (a : Array α) : Array α := Id.run do
  let mut res := a
  let mut rng := mkStdGen
  for i in [0:a.size] do
    let (select, newRng) := randNat rng i (a.size - 1)
    rng := newRng
    res := res.swap! i select
  res

abbrev α : Type := Nat
abbrev β : α → Type := fun _ => Nat

macro "bench(" typ:term "," empty:term "," func:term "," out:ident "," msg:term ")": command => `(
  @[noinline] def run (values : Array Nat) : $typ := Id.run do
    let mut cnt := 0
    let mut m := $empty
    for v in values do
      let m' := $func v v m sorry
      m := m'.1
    return m

  def run' (values : Array α) : IO $typ := do
    return run values

  def $out (values : Array α) : IO Unit := do
    IO.println $msg
    for _ in [:20] do
      let _ ← timeit "" $ run' values
)

@[inline]
def leanInsertIfNew (k : Nat) (v : Nat) (l : Lean.RBMap Nat Nat Ord.compare) (_h : True) :
    { _m : Lean.RBMap Nat Nat Ord.compare // True } :=
  if l.contains k then ⟨l, trivial⟩ else ⟨l.insert k v, trivial⟩

@[inline]
def insertIfNew₁ [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Tree₂ α β l.size (l.size + 1) :=
  if l.contains k then ⟨l, hl, Or.inl rfl⟩ else l.insert k v hl


def insertIfNew₂ [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Tree₂ α β l.size (l.size + 1) :=
  match l with
  | leaf => ⟨.inner 1 k v .leaf .leaf, sorry, sorry⟩
  | l@(inner sz k' v' l' r') =>
      match compare k k' with
      | .lt =>
          let ⟨d, hd, hd'⟩ := insertIfNew₂ k v l' sorry
          ⟨balanceL k' v' d r' sorry sorry sorry, sorry, sorry⟩
      | .gt =>
          let ⟨d, hd, hd'⟩ := insertIfNew₂ k v r' sorry
          ⟨balanceR k' v' l' d sorry sorry sorry, sorry, sorry⟩
      | .eq => ⟨inner sz k' v' l' r', sorry, sorry⟩

bench(Impl Nat (fun _ => Nat), Impl.empty, insertIfNew₁, bench₁, "First")
bench(Impl Nat (fun _ => Nat), Impl.empty, insertIfNew₂, bench₂, "Second")
bench(Impl Nat (fun _ => Nat), Impl.empty, Impl.insertIfNew, bench₃, "Third")
bench(Lean.RBMap Nat Nat Ord.compare, Lean.RBMap.empty, leanInsertIfNew, benchL, "Lean")

def n : Nat := 300000

def mkArr : Array α :=
  fisherYates (Array.range (2 * n) ++ (Array.range n |>.map (·*2)))

def main : IO Unit := do
  let values := mkArr
  bench₁ values
  bench₂ values
  bench₃ values
  benchL values
  bench₁ values
  bench₂ values
  bench₃ values
  benchL values

end Bench.InsertIfNew
