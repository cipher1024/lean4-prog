
import Sat.Advent.IO
import Sat.Tactics
import Sat.Lib.Array.Basic
import Sat.Lib.Classical
import Sat.Lib.Nat
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

namespace Subarray

def size (ar : Subarray α) : Nat := ar.stop - ar.start

def get (ar : Subarray α) (i : Nat) (Hi : i < ar.size) : α :=
have : ar.start + i < Array.size ar.as := by
  have := Nat.add_lt_of_lt_sub_l Hi
  apply Nat.lt_of_lt_of_le this ar.h₂
ar.as.get ⟨ar.start + i, this⟩

def get! [Inhabited α] (ar : Subarray α) (i : Nat) : α :=
ar.as.get! (ar.start + i)

def empty (ar : Subarray α) : Bool := ar.start == ar.stop

@[simp]
theorem stop_popFront (ar : Subarray α) :
  ar.popFront.stop = ar.stop := by
simp [popFront]
byCases h : ar.start < ar.stop <;> simp [*]

@[simp]
theorem size_popFront (ar : Subarray α) :
  0 < ar.size →
  ar.popFront.size = ar.size - 1 := by
intros h
have h : ar.start < ar.stop := by simp [size] at h; assumption
simp [popFront, *, size, Nat.sub_succ]

def extract (ar : Subarray α) (i j : Nat) : Subarray α :=
  let start := min (ar.start + i) ar.stop
  let stop := min (max (ar.start + j) start) ar.stop
  have h₁ : start ≤ stop := by
    simp [Nat.le_min_iff]
    constructor
    focus
      apply Nat.le_max_r
      rewrite [Nat.le_min_iff]
      auto
    . auto
  have h₂ : stop ≤ ar.as.size := by
    apply Nat.min_le_r; apply ar.h₂
  { as := ar.as,
    start := start,
    stop := stop,
    h₁ := h₁,
    h₂ := h₂ }

@[simp]
theorem extract_eq_self (ar : Subarray α) :
  ar.extract 0 ar.size = ar := by
cases ar; simp [extract, size, Nat.add_sub_assoc]
constructor
. auto
. apply Nat.le_max_l; simp [Nat.add_sub_cancel, *]; refl

theorem get_extract (ar : Subarray α) i p q h h' :
  (ar.extract p q).get i h = ar.get (p + i) h' := by
simp [extract, get]
-- have : min (ar.start + p) ar.stop + i = ar.start + (p + i) := sorry
have : ∀ i j, i = j → ar.as.get i = ar.as.get j := by
  intros _ _ h; subst h; refl
apply this; clear this; simp
have : min (ar.start + p) ar.stop = ar.start + p := by
  rw [Nat.min_eq_iff_le_l]
  apply Nat.le_of_lt
  apply Nat.add_lt_of_lt_sub_l
  apply Nat.lt_of_le_of_lt _ h'
  apply Nat.le_add_right
simp [this, Nat.add_assoc]

theorem popFront_extract (ar : Subarray α) p q
  (Hp : p < q)
  (Hq : q ≤ ar.size) :
  (ar.extract p q).popFront  = ar.extract p.succ q := by
have h₄ : p < ar.size := Nat.lt_of_lt_of_le Hp Hq
have H := Nat.add_lt_of_lt_sub_l h₄
simp [extract, popFront]
split <;> simp
next h =>
  have h₀ : min (ar.start + p) ar.stop = ar.start + p := by
    simp [Nat.le_of_lt, *]
  have h₁ : min (ar.start + p).succ ar.stop = (ar.start + p).succ := by
    simp [Nat.succ_le_of_lt, *]
  have h₂ : max q p = q := by
    simp [Nat.le_of_lt, *]
  have h₃ : max q p.succ = q := by
    simp [Nat.le_of_lt, *]; assumption
  simp [h₀, h₁, h₂] at h ⊢
  rw [← Nat.add_succ, Nat.max_add, h₃]
next h =>
  exfalso; apply h; clear h
  have : min (ar.start + p) ar.stop = (ar.start + p) := by
    simp; apply Nat.le_of_lt; assumption
  have : min (ar.start + q) ar.stop = (ar.start + q) := by
    simp [Nat.add_le_iff_l, ar.h₁]; assumption
  have : max q p = q := by
    simp; apply Nat.le_of_lt; assumption
  simp [*]
  apply Nat.add_lt_add_r; auto

theorem size_extract (ar : Subarray α) p q
  (h₀ : p ≤ q) (h₁ : q ≤ ar.size) :
  (ar.extract p q).size = q - p := by
have : min (ar.start + p) ar.stop = ar.start + p :=
  by simp [Nat.add_le_iff_l, ar.h₁]; trans _ <;> assumption
have : max (ar.start + q) ar.start = ar.start + q :=
  by simp [Nat.add_le_iff_r]; apply Nat.le_add_right
have : min (ar.start + q) ar.stop = ar.start + q :=
  by simp [Nat.add_le_iff_l, ar.h₁]; assumption
have : max q p = q := by simp [*]
simp [extract, size, *]
apply congrFun; apply congrArg
rw [Nat.add_comm, ← Nat.add_sub_assoc, Nat.sub_self, Nat.add_zero]
refl

attribute [simp] measure invImage InvImage Nat.lt_wfRel

syntax "prove_decr" : tactic
syntax "decr_step" : tactic
syntax "decr_finish" : tactic

macro_rules
| `(tactic| decr_finish) => `(tactic| assumption)

macro_rules
| `(tactic| decr_finish) => `(tactic| constructor)

macro_rules
| `(tactic| decr_step) => `(tactic| apply Nat.pred_lt; apply Nat.sub_ne_zero)

macro_rules
| `(tactic| decr_step) => `(tactic| apply Nat.sub_lt)

macro_rules
| `(tactic| prove_decr) =>
  `(tactic| { simp [*]; decr_step <;> decr_finish })

def takeWhileAux
            (p : α → Bool) (i : Nat) (ar : Subarray α) : Subarray α :=
if h : i < ar.size then
  if p $ ar.get i h then takeWhileAux p (Nat.succ i) ar
  else ar.extract 0 i
else ar.extract 0 i
termination_by measure λ ⟨_, _, i, ar⟩ => ar.size - i
decreasing_by prove_decr

theorem takeWhileAux_eq (p : α → Bool) (ar : Subarray α) :
  takeWhileAux p i ar =
  if h : i < ar.size then
    if p $ ar.get i h then takeWhileAux p i.succ ar
    else ar.extract 0 i
  else ar.extract 0 i := by
simp only [takeWhileAux]
simp only [takeWhileAux._unary]
rewrite [WellFounded.fix_eq]
refl

def takeWhile (p : α → Bool) (ar : Subarray α) : Subarray α :=
takeWhileAux p 0 ar

def spanAux (p : α → Bool) (i : Nat)
    (ar : Subarray α) : Subarray α × Subarray α :=
if h : i < ar.size then
  if p $ ar.get i h then spanAux p (Nat.succ i) ar
  else (ar.extract 0 i, ar.extract i ar.size)
else (ar.extract 0 i, ar.extract i ar.size)
termination_by measure λ ⟨_, _, i, ar⟩ => ar.size - i
decreasing_by prove_decr

theorem spanAux_eq (p : α → Bool) (i : Nat) (ar : Subarray α) :
  spanAux p i ar =
  if h : i < ar.size then
    if p $ ar.get i h then spanAux p (Nat.succ i) ar
    else (ar.extract 0 i, ar.extract i ar.size)
  else (ar.extract 0 i, ar.extract i ar.size) := by
simp only [spanAux]
simp only [spanAux._unary]
rewrite [WellFounded.fix_eq]
refl

def span (p : α → Bool) (ar : Subarray α) : Subarray α × Subarray α :=
spanAux p 0 ar

def dropWhile
            (p : α → Bool) (ar : Subarray α) : Subarray α :=
if h : 0 < ar.size then
  if p $ ar.get 0 h then dropWhile p ar.popFront
  else ar
else ar
termination_by measure λ ⟨_, _, ar⟩ => ar.size
decreasing_by prove_decr

theorem dropWhile_eq (p : α → Bool) (ar : Subarray α) :
  dropWhile p ar =
  if h : 0 < ar.size then
    if p $ ar.get 0 h then dropWhile p ar.popFront
    else ar
  else ar := by
simp only [dropWhile]
simp only [dropWhile._unary]
rewrite [WellFounded.fix_eq]
refl

theorem Nat.strong_ind {P : Nat → Prop} :
  (∀ x, (∀ y, y < x → P y) → P x) → ∀ a, P a :=
by intros h x; apply Nat.lt_wfRel.wf.induction (C := P) x h

theorem Nat.le_of_not_lt {x y : Nat}
        (h : ¬ y < x) :
  x ≤ y := by
cases Nat.lt_or_ge y x <;> auto

theorem span_eq_takeWhile_dropWhile (p : α → Bool) (ar : Subarray α) :
  ar.span p = (ar.takeWhile p, ar.dropWhile p) := by
simp only [span, takeWhile]
suffices h : ∀ i,
    i ≤ ar.size →
    spanAux p i ar =
    (takeWhileAux p i <| ar,
     dropWhile p <| ar.extract i ar.size) by
  specialize h 0
  simp [h, *, Nat.zero_le]
intros i
generalize hk : (ar.size - i) = k
induction k using Nat.strong_ind generalizing i;
next ih =>
  rw [spanAux_eq, dropWhile_eq, takeWhileAux_eq]
  byCases h₀ : i < size ar <;> simp [*]
  focus
    subst hk
    have : i + 0 < ar.size := by simp [*]
    have h₅ : i ≤ ar.size := Nat.le_of_lt h₀
    have h₄ : ar.size ≤ ar.size := Nat.le_refl _
    have h : 0 < size (extract ar i (size ar)) :=
      by simp [size_extract, *]
    have h₃ : get ar (i + 0) this = get ar i h₀ :=
      by revert this; rw [Nat.add_zero]; intro; refl
    simp [get_extract (h' := this), h, h₃]
    split
    focus
      have : size ar ≤ size ar := by refl
      simp [popFront_extract, *]
      apply ih _ _ _ rfl h₀
      simp [Nat.sub_succ]
      apply Nat.pred_lt
      apply Nat.sub_ne_zero; assumption
    focus
      intros; refl
  focus
    intros h₁; subst hk
    have h₅ : ar.size ≤ i := Nat.le_of_not_lt h₀
    have h₅ := Nat.le_antisymm h₅ h₁
    subst h₅
    have h₄ : ar.size ≤ ar.size := Nat.le_refl _
    have h : ¬ 0 < size (extract ar (size ar) (size ar)) :=
      by simp [size_extract, *]
    simp [*]

end Subarray

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
  else run n' ar.popFront b'
else none
termination_by measure λ ⟨_,ar,_⟩ => ar.size
decreasing_by prove_decr

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

def inputFileName := "Sat/Advent/Day4_input.txt"

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
