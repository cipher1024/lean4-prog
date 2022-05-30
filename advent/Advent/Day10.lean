
import Advent.IO
import Lib.Data.Char
import Lib.Data.HashMap
import Lib.Data.String.Basic
import Std.Data.HashMap
import Std.Data.BinomialHeap

namespace Day10

def examples :=
"[({(<(())[]>[[{[]{<()<>>
[(()[<>])]({[<{<<[]>>(
{([(<{}[<>[]}>{[]{[(<()>
(((({<>}<{<{<>}{[]{[]{}
[[<[([]))<([[{}[[()]]]
[{[{({}]{}}([{[{{{}}([]
{<[[]]>}<{[{[{[]{()[[[]
[<(<(<(<{}))><([]([]()
<{([([[(<>()){}]>(<<{{
<{([{{}}[<[[[<>{}]]]>[]]"

open Std

def bracketPairs : HashMap Char Char :=
[ ('(', ')'),
  ('[', ']'),
  ('{', '}'),
  ('<', '>') ].toHashMap

def pointsTable : HashMap Char Nat :=
[(')', 3),
 (']', 57),
 ('}', 1197),
 ('>', 25137) ].toHashMap

def pointsTable₂ : HashMap Char Nat :=
[(')', 1),
 (']', 2),
 ('}', 3),
 ('>', 4) ].toHashMap
#check Stream
def inputFileName := "Advent/Day10_input.txt"

initialize do
  checkInput "Day10" inputFileName

def checkLine (s : String) : Option Char := Id.run do
  let mut stack := #[]
  for c in s.toArray do
    let c' := stack.get? <| stack.size - 1
    if c' = some c then
      stack := stack.pop
    else if let some c' := bracketPairs.find? c then
      stack := stack.push c'
    else
      return some c
  return none

def fixLine (s : String) : Option String := Id.run do
  let mut stack := #[]
  for c in s.toArray do
    let c' := stack.get? <| stack.size - 1
    if c' = some c then
      stack := stack.pop
    else if let some c' := bracketPairs.find? c then
      stack := stack.push c'
    else
      return none
  return some <| String.mk stack.reverse.toList

structure Median where
  lower : BinomialHeap Nat (. ≥ .) := BinomialHeap.empty
  higher : BinomialHeap Nat (. ≤ .) := BinomialHeap.empty
  med : Option Nat := none
  middle : Option Nat := none

namespace Median

def get? (m : Median) : Option Nat :=
  m.med

def push (med : Median) (x : Nat) : Median :=
(do
  if let some m := med.middle then
    let med' :=
      if m ≤ x then
      { med with
            lower := med.lower.insert m,
            higher := med.higher.insert x,
            middle := none }
      else
      { med with
            lower := med.lower.insert x,
            higher := med.higher.insert m,
            middle := none }
    let l ← med'.lower.head?
    let h ← med'.higher.head?
    some { med' with med := some <| (l + h) / 2 }
  else
    let l ← med.lower.head?
    let h ← med.higher.head?
    if x ≤ l then
      some { med with
           lower := med.lower.tail.insert x,
           middle := some l,
           med := some l }
    else if x ≤ h then
      some { med with
           middle := some x,
           med := some x }
    else
      some { med with
           higher := med.higher.tail.insert x,
           middle := some h,
           med := some h }
  : Option _) |>.getD { med with
                  med := some x
                  middle := some x }

#eval let xs := [1,2,3,7,5,6].foldl push {}
      xs.get?

end Median


def parseInput (lines : Array String) : IO Unit := pure ()

def main : IO Unit := do
let ar ← IO.FS.lines inputFileName
-- let ar ← lines examples
let mut res := #[]
let mut i := 0
let mut total := 0
let mut scores := #[]
let mut med : Median := {}
for ln in ar do
  if let some r := fixLine ln then
    let score := r.foldl
       (λ acc c => acc * 5 + pointsTable₂.find! c) 0
    med := med.push score
    scores := scores.push score
    total := total + score
    res := res.push (i, r)
  i := i + 1
IO.println med.get?
IO.println scores

#eval main

end Day10
