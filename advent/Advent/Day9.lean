
import Std.Data.HashSet
import Lib.Data.String.Basic
import Lib.Meta.Dump
import Advent.IO

namespace Day9

def examples :=
"2199943210
3987894921
9856789892
8767896789
9899965678"

def inputFileName := "Advent/Day9_input.txt"

initialize do
  checkInput "Day9" inputFileName

def Grid := Array (Array Nat)
  deriving ToString

instance [Monad m] : ForIn m Grid (Array Nat) :=
inferInstanceAs (ForIn m (Array (Array Nat)) (Array Nat))

def Grid.dim (g : Grid) : Nat × Nat :=
(g.size, g[0].size)

def Grid.get' (g : Grid) (x y : Nat) : Nat :=
let x := do
  guard (x >= 1)
  let ln ← g.get? (x - 1)
  guard (y >= 1)
  ln.get? (y - 1)
match x with
| some c => c
| none => 20

def Grid.neighborhood' (g : Grid) (x y : Nat) :
    Array Nat :=
#[ g.get' (x-1) y, g.get' (x+1) y,
   g.get' x (y-1), g.get' x (y+1) ]

def Grid.isLowpoint (g : Grid) (x y : Nat) : Bool :=
let h := g.get' x y
g.neighborhood' x y |>.all λ h' => h < h'

def Grid.neighborhood (g : Grid) (x y : Nat) :
    Array Nat :=
g.neighborhood' x y

def Grid.get (g : Grid) (x y : Nat) : Nat :=
Grid.get' g x y

def set (g : Array (Array α)) (x y : Nat) (v : α) :
    Array (Array α) :=
Array.modify g (x-1) (Array.set! . (y-1) v)

open Std

partial def Grid.basin (g: Grid) (x y : Nat)
        (f : Nat → Nat → Nat → β → β)
        (x₀ : β) : β :=
  let (m,n) := g.dim
  let _ : Inhabited β := ⟨ x₀ ⟩
  let rec loop [Inhabited β] (x y : Nat) (ar : HashSet (Nat × Nat))
          (source : Nat) (x₀ : β) : HashSet (Nat × Nat) × β :=
    if ¬ ar.contains (x, y) ∧
       1 ≤ x ∧ x ≤ m ∧
       1 ≤ y ∧ y ≤ n ∧
       g.get x y < 9 ∧
       source < g.get x y + 1 then
        let source := g.get x y + 1
        let ar' := ar.insert (x, y)
        let s := f x y (g.get x y) x₀
        let (ar',s) := loop (x - 1) y ar' source s
        let (ar',s) := loop (x + 1) y ar' source s
        let (ar',s) := loop x (y - 1) ar' source s
        loop x (y + 1) ar' source s
    else (ar,x₀)
  loop x y mkHashSet 0 x₀ |>.2

def insert (x : Nat) : List Nat → List Nat
| [] => [x]
| y :: ys =>
  if x < y then
    y :: insert x ys
  else
    x :: y :: ys

def pushMax3 (x : Nat) (ar : List Nat) : List Nat :=
insert x ar |>.take 3

def parseInput (lines : Array String) : IO Grid := do
let lns := lines.map <| Array.map String.singleton ∘ String.toArray
lns.mapM (Array.mapM parseNat)

def main : IO Unit := do
let ar ← parseInput <| (← IO.FS.lines inputFileName)
-- let ar ← parseInput <| (← lines examples)
let (m,n) := ar.dim
println!"Dim: {(m,n)}"
let mut risk := 0
let mut low := #[]
for i in [1:m+1] do
  for j in [1:n+1] do
    if ar.isLowpoint i j then
      risk := risk + ar.get i j + 1
      low := low.push (i,j)
println!"{dump! risk}"
-- println!"{dump! low}"
let mut basin := #[]
let mut basinSize := #[]
let mut ar' := ar.map (. |>.map λ _ => " ")
let mut max := []
for (i,j) in low do
  let shape := ar.basin i j (λ x y i ar => set ar x y ".") ar'
  let size := ar.basin i j (λ _ _ _ acc => acc + 1) 0
  max := pushMax3 size max
  basin := basin.push shape
  basinSize := basinSize.push size
println!"{dump! basinSize}"
println!"{dump! max}"
println!"{dump! Foldable.product max}"
-- for lns in basin do
--   for ln in lns do
--     println!"{ln}"
--   println!"***"

#eval main

end Day9
