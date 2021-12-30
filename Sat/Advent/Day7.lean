
import Sat.Lib.Nat
import Sat.Lib.Equiv
import Sat.Quot
import Sat.Tactics
import Sat.Advent.IO


-- (lean--version)
-- ("4" "0" "0-nightly-2021-12-05")

section day7

def dist (i j : Nat) : Nat := max (i - j) (j - i)

def cost (input : Array Nat) (i : Nat) : Nat :=
input.foldl (λ acc pos => acc + dist pos i) 0

end day7

def Array.max (ar : Array Nat) : Nat :=
ar.foldl _root_.max 0

def Array.min (ar : Array Nat) : Nat :=
if h : ar.size > 0 then
  ar.foldl _root_.min <| ar.get ⟨_, h⟩
else
  0

namespace Day7

def examples :=
"16,1,2,0,4,2,7,1,2,14"

def parseInput (input : String) : IO (Array Nat) := do
Array.mk <| (← input.splitOn "," |>.mapM parseNat)

def inputFileName := "Sat/Advent/Day7_input.txt"

def main : IO Unit := do
-- let ar ← parseInput <| (← IO.FS.lines inputFileName).get! 0
let ar ← parseInput examples
IO.println <| cost ar 2
IO.println <| cost ar 3
IO.println <| cost ar 4
IO.println <| cost ar 5
IO.println <| cost ar 1

#eval main

end Day7
