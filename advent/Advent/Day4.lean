
import Advent.IO
import Lib.Logic.Classical
import Lib.Data.Array.Basic
import Lib.Data.Nat
import Lib.Tactic
import Std.Data.HashMap

def Dim := 5

structure Board where
mkImpl ::
  cells : Grid Dim Dim Nat
  marked : Grid Dim Dim Bool
  locs : Std.HashMap Nat (Fin Dim × Fin Dim)
  rows : Buffer Dim Nat
  cols : Buffer Dim Nat
  -- diag₀ : Nat
  -- diag₁ : Nat

instance : ToString Board where
  toString x :=
    let mark (x : Nat)
        | true => s!"({x})"
        | false => s!" {x} "
    let cells := x.cells.zipWith mark x.marked
    let inner := String.intercalate ",\n   " $
      cells.cells.cells.map (toString ∘ Buffer.cells) |>.toList
    s!"#[ {inner} ]"

namespace Board

@[inline]
def foldlIdx₂
    (ar : Grid m n α) (f : Fin m → Fin n → α → β → β) (x₀ : β) : β :=
ar.foldlIdx f x₀

def mk (cells : Array (Array Nat)) : OptionM Board := do
let cells ← Grid.mk cells
return {
    cells := cells,
    marked := cells.map λ _ => false,
    locs := foldlIdx₂ cells (λ i j x m => m.insert x (i, j)) (Std.mkHashMap 10),
    rows := Buffer.mkFilled Dim
    cols := Buffer.mkFilled Dim
    -- diag₀ := Dim
    -- diag₁ := Dim
  }

def Fin.max {n : Nat} m (h : m = Nat.succ n) : Fin m :=
⟨n, h ▸ Nat.lt_succ_self _ ⟩

def score (n : Nat) (b : Board) : Bool × Board := Id.run $ do
let some (i, j) ← b.locs.find? n | return (false, b)
-- let false       ← b.marked.get i j | return (false, b)
if ¬ b.marked.get i j then
  let b' := { b with
    marked := b.marked.set i j true
    rows := b.rows.modify i Nat.pred
    cols := b.cols.modify j Nat.pred }
    -- diag₀ := if i = j then b.diag₀ - 1 else b.diag₀
    -- diag₁ := if Fin.max Dim rfl - i = j then b.diag₁ - 1 else b.diag₁ }
  let win : Bool := b'.rows.get i = 0 ∨ b'.cols.get j = 0
  return(win, b')
else return (false, b)

end Board

section Logic

theorem And.congr {p p' q q'}
        (hp : p ↔ p')
        (hq : q ↔ q') :
  p ∧ q ↔ p' ∧ q' := by simp [*]

theorem And.congr_left {p p' q}
        (Hp : p ↔ p') :
  p ∧ q ↔ p' ∧ q :=
by apply And.congr <;> simp [*]

theorem And.congr_right {p q q'}
        (Hp : q ↔ q') :
  p ∧ q ↔ p ∧ q' :=
by apply And.congr <;> simp [*]

end Logic

structure Game where
  draw : Array Nat
  boards : Array Board

def Board.partRun (ar : Subarray Nat) (b : Board) : (n : Nat) → Board
| 0 => b
| Nat.succ n =>
if hsize : 0 < ar.size then
  let (_, b') := b.score $ ar.get 0 hsize
  partRun ar.popFront b' n
else
  b

def Board.sum (b : Board) : Nat :=
let unmarked x b := if b then 0 else x
(b.cells.zipWith unmarked b.marked).foldl (.+.) 0

def Board.run (n : Nat) (ar : Subarray Nat) (b : Board) :
  Option (Nat × Nat) :=
if hsize : 0 < ar.size then
  -- trace[foo] b'
  let draw := ar.get 0 hsize
  let (win, b') := b.score draw
  let n' := n + 1
  if win then
    let score := b'.sum * draw
    some (n', score)
  else
    have : ar.popFront.size < ar.size := by
      simp [*]; auto [Nat.sub_lt]
    run n' ar.popFront b'
else none
termination_by run ar _ => ar.size
-- decreasing_by prove_decr

def Option.combine (f : α → α → α) : Option α → Option α → Option α
| none, x => x
| x, none => x
| some x, some y => some $ f x y

def parseDraws (input : String) : IO (Array Nat) :=
(input.splitOn ",").toArray.mapM parseNat

partial def parseBoards (input : Subarray String) : IO (Array Board) :=
  let rec go (ar : Array Board) input := do
    let input := input.dropWhile String.isEmpty
    let (board, input) := input.span (not ∘ String.isEmpty)
    if board.size = 0 then
      return ar
    else do
      let x := Board.mk (← board.toArray.mapM
               λ x => (String.splitOn x " "
                      |>.filter (not ∘ String.isEmpty)
                      |>.toArray.mapM parseNat))
      match x with
       | some x => go (ar.push x) input
       | none => throw (IO.userError "parsing error")
  go (Array.mkEmpty 10) input

def parseInput (input : Array String) : IO Game := do
  let first := input.get! 0
  let input := input[1:]
  let draws ← parseDraws first
  let boards ← parseBoards input
  -- IO.println draws
  -- for x in boards do
  --   IO.println $ x.run 0 draws.toSubarray
  --   IO.println $ x.partRun draws.toSubarray 12

  return ⟨draws, boards⟩

-- Part 1
def Game.findWinner (g : Game) : Option Nat := OptionM.run $ do
let combine : Nat × Nat → Nat × Nat → Nat × Nat
    | ⟨n,score⟩, ⟨n',score'⟩ =>
      if n > n' then ⟨n,score⟩ -- <- Part 2
      else ⟨n', score'⟩
let go (acc : Option (Nat × Nat)) (b : Board) :=
    Option.combine combine acc $ b.run 0 g.draw.toSubarray
let (r, score) ← g.boards.foldl go none
return score

namespace Day4

def inputFileName := "Advent/Day4_input.txt"

def examples :=
"7,4,9,5,11,17,23,2,0,14,21,24,10,16,13,6,15,25,12,22,18,20,8,19,3,26,1

22 13 17 11  0
 8  2 23  4 24
21  9 14 16  7
 6 10  3 18  5
 1 12 20 15 19

 3 15  0  2 22
 9 18 13 17  5
19  8  7 25 23
20 11 10 24  4
14 21 16 12  6

14 21 17 24  4
10 16 15  9 19
18  8 23 26 20
22 11 13  6  5
 2  0 12  3  7"

def main : IO Unit := do
  -- let g ← parseInput $ lines examples
  let g ← parseInput (← IO.FS.lines inputFileName)
  IO.println $ g.findWinner
  IO.println "hello world"

#eval main

end Day4
