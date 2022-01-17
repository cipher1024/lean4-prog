import Lib.Data.Array.Basic
import Advent.IO
import Advent.Day1

-- #check Array.size_map

namespace Window

def get! (w : Window) (i : Nat) : Nat :=
w.values.get! $ (i+w.head') % w.values.size

def modify (w : Window) (i : Nat) (f : Nat → Nat) : Window where
  values := w.values.modify ((i+w.head') % w.values.size) f
  head' := w.head'
  head_lt := by simp [w.head_lt]

end Window

def Population := Window

namespace Population

def mk (n : Nat) (ar : Array Nat) : Population :=
ar.foldl (λ w i => w.modify i (. + 1)) <| Window.mk n

instance : ToString Population where
  toString x :=
    let N := x.values.size
    let offset := N - x.head
    toString $ Array.concatMap id
      <| x.values.mapIdx
      <| λ i n => Array.mkArray n ((i.val + offset) % N)

def age (p : Population) : Population :=
let head := p.current
p.push 0
  |>.modify 8 (. + head)
  |>.modify 6 (. + head)

def count (p : Population) (days : Nat) : Nat :=
days.repeat age p |>.values |>.foldl (.+.) 0

end Population

namespace Day6

def parseInput (input : String) : IO (Array Nat) := do
Array.mk <| (← input.splitOn "," |>.mapM parseNat)

def examples :=
"3,4,3,1,2"

def inputFileName' := "Advent/Day6_input.txt"

def main' : IO Unit := do
let ar ← parseInput <| (← IO.FS.lines inputFileName').get! 0
let p := Population.mk 9 ar
-- let p := p.age
-- let p := p.age
-- let p := p.age
-- let p := p.age
-- let p := p.age
-- let w : Window := p
IO.println $ p.count 256
-- IO.println $ w
-- IO.println $ w.current

#eval main'

end Day6
