
import Sat.Lib.Nat
import Sat.Lib.Array.Instances
import Sat.Lib.Equiv
import Sat.Lib.Fold
import Sat.Lib.Traversable
import Sat.Quot
import Sat.Tactics
import Sat.Advent.IO

-- (lean--version)
-- ("4" "0" "0-nightly-2021-12-05")

section day7

def dist (i j : Nat) : Nat := max (i - j) (j - i)

def cost (input : Array Nat) (i : Nat) : Nat :=
input.foldl (λ acc pos => acc + dist pos i) 0

def resize (ar : Array α) (x : α) (i : Nat) : Array α :=
if i < ar.size
then ar
else ar ++ Array.mkArray (i - ar.size + 1) x

theorem lt_size_resize {ar : Array α} {x : α} {i : Nat} :
  i < (resize ar x i).size := by
simp [resize]; split
. assumption
next h =>
have h := Nat.le_of_not_gt h
simp [*]

def modifyResize
  (ar : Array α) (i : Nat) (f : α → α) (y : α) : Array α :=
let ar := resize ar y i
let i : Fin ar.size := ⟨i, lt_size_resize⟩
ar.set i (f <| ar.get i)

def posToCount (ar : Array Nat) : Array Nat :=
ar.foldl (λ ar x => modifyResize ar x Nat.succ 0) #[]

def linearCost : Fold Nat Nat :=
Prod.snd <$> Fold.mk (0, 0)
  (λ (num, costAccum) n =>
    (num + n, costAccum + num))

def costUp : Array Nat → Array Nat :=
linearCost.scanl
-- scanl (λ n (num, costAccum) => (costAccum + num, (num + n, costAccum + num))) (0, 0)

def costDown : Array Nat → Array Nat :=
scanr (λ n (num, costAccum) => (costAccum + num, (num + n, costAccum + num)))
  (0, 0)

def cost' (input : Array Nat) : Array Nat :=
  let counts := posToCount input
  let lr := costUp counts
  let rl := costDown counts
  Array.zipWith lr rl (.+.)

def minCost (input : Array Nat) : Option (Nat × Nat) :=
cost' input |>.foldlIdx
  (λ i x => λ
    | Option.some ((a, b) : Nat × Nat) =>
      if x < b then some (i, x)
      else some (a, b)
    | Option.none => some (i, x) )
  none

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
-- #check elab
-- #check Lean.PrettyPrinter.ppTerm
-- #check Lean.MonadQuotation
-- #print Lean.Syntax
-- #print Lean.Elab.TermElabM
-- #print Lean.MacroM
-- #print Lean.MetaM
-- #check Lean.Syntax

-- #check Lean.MonadRef

def main : IO Unit := do
let pos ← parseInput <| (← IO.FS.lines inputFileName).get! 0
-- let pos ← parseInput examples
let count ← posToCount pos
-- IO.println <| pos.size
-- IO.println <| count
-- IO.println <| posToCount pos
IO.println <| dump! minCost pos
-- IO.println <| dump! costUp count
-- IO.println <| dump! costDown count
-- IO.println <| dump! cost' pos

#eval main

end Day7
