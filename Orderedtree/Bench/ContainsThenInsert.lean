/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DOrderedTree.Internal.Impl
import Lean.Data.RBMap

namespace Bench.ContainsThenInsert

open Std.DOrderedTree.Internal Impl

abbrev α : Type := Nat
abbrev β : α → Type := fun _ => Nat

macro "bench(" typ:term "," empty:term "," func:term "," out:ident "," msg:term ")": command => `(
  @[noinline] def run (values : Array Nat) : Nat × $typ := Id.run do
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

@[inline]
def containsThenInsert₁ [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Bool × TreeB α β l.size (l.size + 1) :=
  (l.contains k, l.insert k v hl)

@[inline]
def containsThenInsert₂ [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Bool × TreeB α β l.size (l.size + 1) :=
  let sz := size l
  let m := l.insert k v hl
  (sz == m.1.size, m)
where -- workaround for https://github.com/leanprover/lean4/issues/6058
  size : Impl α β → Nat
  | leaf => 0
  | inner sz _ _ _ _ => sz

def containsThenInsert₃ [Ord α] (k : α) (v : β k) (l : Impl α β) (hl : l.Balanced) :
    Bool × TreeB α β l.size (l.size + 1) :=
  match l with
  | leaf => ⟨false, .inner 1 k v .leaf .leaf, sorry, sorry, sorry⟩
  | inner sz k' v' l r =>
      match compare k k' with
      | .lt =>
          let ⟨c, ⟨d, hd, hd', hd''⟩⟩ := containsThenInsert₃ k v l sorry
          ⟨c, balanceL k' v' d r sorry sorry sorry, sorry, sorry, sorry⟩
      | .gt =>
          let ⟨c, ⟨d, hd, hd', hd''⟩⟩ := containsThenInsert₃ k v r sorry
          ⟨c, balanceR k' v' l d sorry sorry sorry, sorry, sorry, sorry⟩
      | .eq => ⟨true, .inner sz k v l r, sorry, sorry, sorry⟩

bench(Impl Nat (fun _ => Nat), Impl.empty, containsThenInsert₁, bench₁, "First")
bench(Impl Nat (fun _ => Nat), Impl.empty, containsThenInsert₂, bench₂, "Second")
bench(Impl Nat (fun _ => Nat), Impl.empty, containsThenInsert₃, bench₃, "Third")
bench(Lean.RBMap Nat Nat Ord.compare, Lean.RBMap.empty, leanContainsThenInsert, bench₄, "Fourth")

def n : Nat := 150000

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

end Bench.ContainsThenInsert
