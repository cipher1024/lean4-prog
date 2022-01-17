
import Advent.IO
import Std.Data.HashMap

open Std (HashMap)

namespace Day5

def Grid := HashMap (Nat × Nat) Nat

structure Line where
  x : Nat
  y : Nat
  x' : Nat
  y' : Nat
deriving Repr, Inhabited

instance : ToString Line where
  toString
    | ⟨x,y,x',y'⟩ => s!"{x},{y} -> {x'},{y'}"

def Array.range (p q : Nat) : Array Nat :=
if p < q
  then Array.mk $ List.range (q - p + 1) |>.map (p + .)
  else Array.mk $ List.range (p - q + 1) |>.map (q + .) |>.reverse

def coords (k : Line) : Array (Nat × Nat) :=
if k.x = k.x' then
  let y := min k.y k.y'
  let y' := max k.y k.y'
  Array.mk <| List.range (y' - y + 1) |>.map (k.x, y + .)
else if k.y = k.y' then
  let x := min k.x k.x'
  let x' := max k.x k.x'
  Array.mk <| List.range (x' - x + 1) |>.map (x + ., k.y)
else
  Array.range k.x k.x' |>.zip <| Array.range k.y k.y'

abbrev Parser := EStateM String Substring

def Parser.run (p : Parser α) (input : String) : IO α :=
match EStateM.run p input.toSubstring with
| EStateM.Result.ok r s ..  => return r
| EStateM.Result.error e s ..  => throw $ IO.userError e

namespace Parser

def parseNat : Parser Nat := do
let input ← get
let input := input.dropWhile (not ∘ Char.isDigit)
let x := input.takeWhile Char.isDigit
set $ input.dropWhile Char.isDigit
match x.toNat? with
| none => throw "invalid nat"
| some n => return n

def parseLine : Parser Line := do
return { x := (← parseNat)
         y := (← parseNat)
         x' := (← parseNat)
         y' := (← parseNat) }

def parseInput (input : Array String) : IO (Array Line) :=
input.mapM <| parseLine.run

end Parser

def processLine : Nat × Grid → Line → Nat × Grid
| g, ln =>
  let mark : Nat × Grid → Nat × Nat → Nat × Grid
      | ⟨n, g⟩, pt =>
        let c := g.findD pt 0 + 1
        let g' := g.insert pt c
        if c = 2 then ⟨n+1, g'⟩
        else ⟨n, g'⟩
  coords ln |>.foldl mark g

def processLines (lns : Array Line) : Nat × Grid :=
lns.foldl processLine (0, Std.mkHashMap)
-- let (x, input) := input.span Char.isDigit
-- let (x, input) := input.dropWhile (not ∘ Char.isDigit) |>.span Char.isDigit

def inputFileName := "Advent/Day5_input.txt"

def examples :=
"0,9 -> 5,9
8,0 -> 0,8
9,4 -> 3,4
2,2 -> 2,1
7,0 -> 7,4
6,4 -> 2,0
0,9 -> 2,9
3,4 -> 1,4
0,0 -> 8,8
5,5 -> 8,2"

def main : IO Unit := do
-- let lns := lines examples
let lns ← IO.FS.lines inputFileName
let lns ← Parser.parseInput lns
-- let lns : Array _ := lns[:6]
let ⟨c, m⟩ := processLines <| lns
-- IO.println m.toList
IO.println <| c
-- for x in lns[:3] do
--   IO.println ""
--   IO.println <| x
--   IO.println <| coords x
-- IO.println <| lns.size

#eval main

end Day5
