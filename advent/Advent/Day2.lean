
inductive Direction :=
| Up | Down | Forward
deriving Repr

instance : ToString Direction := ⟨reprStr⟩

def Step := Direction × Nat

instance : ToString Step :=
inferInstanceAs (ToString (Direction × Nat))

def makeStep (d : Direction) (kw : String) (ln : String) : Option Step :=
if kw.isPrefixOf ln
then Prod.mk d <$> String.toNat? (ln.drop kw.length)
else none

open Direction

def parseStep (ln : String) : IO Step :=
let r :=
  makeStep Up "up " ln <|>
  makeStep Down "down " ln <|>
  makeStep Forward "forward " ln
match r with
| some s => pure s
| none => throw (IO.userError "parsing error")

namespace Day2

def examples :=
"forward 5
down 5
forward 8
up 3
down 8
forward 2"

-- Part 1
def runStep : Nat × Nat → Step → Nat × Nat
| ⟨h, v⟩, (Up, dist) => ⟨h, v - dist⟩
| ⟨h, v⟩, (Down, dist) => ⟨h, v + dist⟩
| ⟨h, v⟩, (Forward, dist) => ⟨h + dist, v⟩

def runTractory (l : Array Step) : Nat × Nat :=
l.foldl runStep (0, 0)

-- Part 2
def runStep' : Nat × Nat × Nat → Step → Nat × Nat × Nat
| ⟨h, v, aim⟩, (Up, dist) => ⟨h, v, aim - dist⟩
| ⟨h, v, aim⟩, (Down, dist) => ⟨h, v, aim + dist⟩
| ⟨h, v, aim⟩, (Forward, dist) => ⟨h + dist, v + dist*aim, aim⟩

def runTractory' (l : Array Step) : Nat × Nat × Nat :=
l.foldl runStep' (0, 0, 0)
def inputFileName := "Advent/Day2_input.txt"

def main : IO Unit := do
IO.println (← System.FilePath.pathExists inputFileName)
IO.println "hello world"
-- let lns := (examples.splitOn "\n").toArray
let lns ← IO.FS.lines inputFileName
let ⟨h,v,_⟩ := runTractory' (← lns.mapM parseStep)
IO.println (h * v)

#eval main

end Day2
