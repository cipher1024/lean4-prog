
import Advent.IO
import Lib.Data.Array.Basic

def measurements_ex : Array Nat :=
#[199,
  200,
  208,
  210,
  200,
  207,
  240,
  269,
  260,
  263]

def inputFileName := "Advent/Day1_input.txt"

def readInput : IO (Array Nat) := do
let x ← IO.FS.lines inputFileName
x.mapM parseNat

-- Part 1
def countIncreases (ar : Array Nat) : Nat :=
let count : Nat × Nat → Nat → Nat × Nat
    | ⟨prev, acc⟩, val =>
      if prev < val then ⟨val, acc + 1⟩
      else ⟨val, acc⟩
((ar.toSubarray 1).foldl count (ar.get! 0, 0)).2

structure Window where
mkImpl ::
  values : Array Nat
  head' : Nat
  head_lt : head' < values.size

namespace Window

instance : ToString Window where
  toString w :=
    let z := w.values[ w.head' : ] ++ w.values[ 0 : w.head']
    toString z

def mk (size : Nat) : Window where
  values := Array.mkArray (max size 1) 0
  head' := 0
  head_lt := by
    simp
    have : 1 ≤ max size 1 := by
      simp [max]
      byCases h : 1 < size <;> simp [*]
      apply Nat.le_of_lt h
    apply Nat.lt_of_lt_of_le _ this
    apply Nat.zero_lt_one

protected def size (w : Window) : Nat := w.values.size

protected def head (w : Window) : Fin w.size := ⟨w.head', w.head_lt⟩

def push (x : Nat) (w : Window) : Window where
  values := w.values.set w.head 0 |>.map (x+·)
  head' := (w.head' + 1) % w.size
  head_lt := by
    simp [Window.size]
    apply Nat.mod_lt
    apply Nat.lt_of_le_of_lt _ w.head_lt
    apply Nat.zero_le

def current (w : Window) : Nat := w.values.get w.head

end Window

-- Part 2
def countWindowIncreases (ar : Array Nat) : Nat :=
let windowSize := 3
let first := ar[0 : 3].foldl (flip Window.push) (Window.mk windowSize)
let count : Window × Nat → Nat → Window × Nat
    | ⟨prev, acc⟩, val =>
      let sum₀ := prev.current
      let next := prev.push val
      let sum := next.current
      if sum₀ < sum then ⟨next, acc + 1⟩
      else ⟨next, acc⟩
((ar.toSubarray 3).foldl count (first, 0)).2

namespace Day1

def main : IO Unit := do
IO.println "hello"
IO.println measurements_ex
IO.println (← IO.currentDir)
let input ← readInput
IO.println $ countWindowIncreases input

end Day1
