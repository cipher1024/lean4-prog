
import Std.Data.HashMap

import Lib.Data.Array.Basic
import Lib.Data.Array.Instances
import Lib.Data.Char
import Lib.Data.Foldable
import Lib.Data.HashSet
import Lib.Data.String.Basic
import Advent.IO

namespace Day8
open Std
def patt : Array String :=
#[ "abcefg",  -- 0
   "cf",      -- 1
   "acdeg",   -- 2
   "acdfg",   -- 3
   "bcdf",    -- 4
   "abdfg",   -- 5
   "abdefg",  -- 6
   "acf",     -- 7
   "abcdefg", -- 8
   "abcdfg"   -- 9
  ]

def vDash (b : Bool) : String :=
if b then
"  " ++ Nat.repeat (.++ "-") 7 "" ++ "  "
else
"  " ++ Nat.repeat (.++ " ") 7 "" ++ "  "

def hDash (b1 b2 : Bool) : String :=
let l := if b1 then "| " else "  "
let r := if b2 then " |" else "  "
l ++ Nat.repeat (.++ " ") 7 "" ++ r

def render (s : String) : String :=
let ln1 := vDash (s.contains 'a')
let ln2 := hDash (s.contains 'b') (s.contains 'c')
let ln3 := vDash (s.contains 'd')
let ln4 := hDash (s.contains 'e') (s.contains 'f')
let ln5 := vDash (s.contains 'g')
String.intercalate "\n"
<| [ln1] ++ Nat.repeat (ln2 :: .) 5 [] ++
   [ln3] ++ Nat.repeat (ln4 :: .) 5 [] ++
   [ln5]

-- #eval IO.println <| render <| patt.get! 0

-- #exit
def patRev : HashMap String Nat :=
patt.foldlIdx (λ i k m => m.insert k i) mkHashMap

def patt' : Array (HashSet Char) :=
patt.map (. |>.toList |>.toHashSet)

def counts : HashMap Nat (Array Nat) :=
patt.foldlIdx
  (λ i n acc =>
    let ar := acc.findD n.length #[]
    acc.insert n.length <| ar.push i)
  mkHashMap

def Subst := HashMap Char (HashSet Char)
  deriving Inhabited

def Subst.insert (s : Subst) (xs : String) (ys : HashSet Char) :
    Option Subst := Id.run do
  let mut s := s
  for c in xs.toList do
    let ρ := s.find! c |>.intersect ys
    if ρ.isEmpty then
      return none
    s := HashMap.insert s c ρ
  return some s
-- xs.foldlM (λ s c => s.modify? c <| ys.intersect) s
-- #exit

structure Key where
mkImpl ::
  subst : Subst
  fullSubst : HashMap Char Char
  decoded : HashMap String Nat
  unprocessed : Array String
  processed : Array String

def Key.mk (ar : Array String) : Key where
  subst := "abcdefg".foldl
    (λ h c => HashMap.insert h c "abcdefg".toList.toHashSet)
    mkHashMap
  fullSubst := mkHashMap
  decoded := mkHashMap
  unprocessed := ar
  processed := #[ ]

def Key.process (k : Key) : Key := Id.run do
  let mut unprocessed : Array String := #[]
  let mut processed := k.processed
  let mut subst := k.subst
  let mut decoded := k.decoded
  for s in k.unprocessed do
    let candidates := counts.find! s.length
    -- let r := candidates.map patt'.get!
    let xs := candidates.filterMap λ n =>
      (n,.) <$> subst.insert s (patt'.get! n)
    if xs.size = 1 then
      subst := xs[0].2
      decoded := decoded.insert s xs[0].1
      processed := processed.push s
    else
      unprocessed := unprocessed.push s
  { processed := processed,
    unprocessed := unprocessed,
    subst := subst,
    decoded := decoded,
    fullSubst := k.fullSubst }

partial def Key.propagateUnits (k : Key) : Key := Id.run do
  let rec loop s subst fullSubst := Id.run do
    let mut s := s
    let mut subst := subst
    let mut changed := false
    let mut fullSubst := fullSubst
    for (k,v) in subst.toList do
      if v.size = 1 then
        let n := s.size
        s := s.union v
        changed := changed || s.size != n
        if s.size != n then
          fullSubst := fullSubst.insert k <| v.toArray[0]
      else
        subst := HashMap.insert subst k <| v.difference s
    if changed then
      loop s subst fullSubst
    else
      return { k with subst := subst,
                      fullSubst := fullSubst }
  loop mkHashSet k.subst k.fullSubst

instance : Decidable (Char.lt c₀ c₁) :=
inferInstanceAs (Decidable (c₀.val < c₁.val))

def Key.apply (k : Key) (s : String) : Option Nat :=
OptionM.run do
  let s' ← s.toArray.mapM <| HashMap.find? k.fullSubst
  let s' := String.mk
         <| s'.qsort (λ c₀ c₁ => (Char.lt c₀ c₁)) |>.toList
  patRev.find? s'

def Key.use (k : Key) : Key := Id.run do
  let mut unprocessed := #[]
  let mut processed := k.processed
  let mut decoded := k.decoded
  for s in k.unprocessed do
    if let some s' ← k.apply s then
      processed := processed.push s
      decoded := decoded.insert s s'
    else unprocessed := unprocessed.push s
  { k with unprocessed := unprocessed,
           processed := processed,
           decoded := decoded }

def Key.measure (k : Key) :=
( k.decoded.size, k.fullSubst.size,
  k.processed.size, k.unprocessed.size)

def SearchM (α : Type u) :=
∀ s : Type u, (α → Option s) → Option s

instance : Monad SearchM where
  pure x := λ s f => f x
  bind x f := λ s g =>
    x s λ a => f a _ g

instance : Alternative SearchM where
  failure s f := none
  orElse x y s f :=
    x _ f <|> y () _ f
-- def Key.search

instance : Coe (OptionM α) (SearchM α) where
  coe x s f := OptionM.run <| x >>= f

instance : Coe (Option α) (SearchM α) where
  coe x s f := OptionM.run <| x >>= f

def pick (ar : Array α) : SearchM α :=
λ s f => OptionM.run <| Array.firstM f ar

def SearchM.run (x : SearchM α) : OptionM α := x _ some

def Key.guess (k : Key) : OptionM Key :=
SearchM.run do
  let mut k := k
  let mut s := mkHashSet
  for (c,vs) in k.subst.toArray.qsort
      (λ x y => x.2.size < y.2.size) do
    if ¬ k.fullSubst.contains c then
      let v ← pick (vs.difference s).toArray
      s := s.insert v
      k := { k with fullSubst := k.fullSubst.insert c v }
    else
      s := s.insert <| k.fullSubst.find! c
  if let some r := OptionM.run <| k.unprocessed.mapM k.apply then
    for str in k.unprocessed do
      let s' : Nat ← k.apply str
      -- if ¬ patRev.contains s' then
        -- dbgTrace s!"here: {s'}" (λ x => x)
        -- dbgTrace s!"here: {patRev.toList}" (λ x => x)
      -- let s' := patRev.find! s'

      k := { k with
        processed := k.processed.push str,
        decoded := k.decoded.insert str s' }
    k
  else
    failure

partial def Key.round (k : Key) (bound := 7) : Key :=
  let m := k.measure
  let k' := k.process.propagateUnits.use
  -- let k' := k
  if let some k' := OptionM.run k'.guess then
    k'
  else
    if k'.measure == m || bound == 0 then k'
    else round k' (bound - 1)

-- let candidates := counts.find! s.length
-- -- dbgTrace s!"counts: {r}" λ _ =>
-- if candidates.size = 1 then
--   let r := candidates.map patt'.get!
-- -- dbgTrace s!"s: {s.length}" λ _ =>
-- -- dbgTrace s!"r: {r.map (. |>.toList)}" λ _ =>
--   let subst := s.foldl
--       (λ k c => k.modify? c <| r.foldl HashSet.intersect)
--       k.subst
--   { k with decoded := k.decoded.insert s candidates[0],
--            subst := subst }
-- --   k
-- -- -- k.modifyD _ _ _
-- else
--   k

-- def Key.update (ar : Array String) (k : Key) : Key :=
-- let k := ar.foldl Key.insert k
-- let k : Key × HashSet Char :=
--   k.fold
--     (λ (k, s) c v =>
--       if v.size = 1
--         then (HashMap.insert k c v, s.union v)
--         else (HashMap.insert k c (v.difference s), s) )
--     (mkHashMap, mkHashSet)
-- k.1
-- k

-- def Key.toSubst (k : Key) : Option (HashMap Char Char) :=
-- OptionM.run <| k.subst.foldM
--   (λ r k s =>
--     match s.toList with
--     | [x] => pure <| r.insert k x
--     | _ => none )
--   mkHashMap

def decode (s : String) : Option Nat :=
match counts.find? s.length with
| some #[a] => some a
| _ => none

def decode₂ (s : Array (Array String)) :
    Option (Array Nat × Array Nat) :=
OptionM.run do
  let x := s[0]
  let y := s[1]
  let k := Key.mk <| x ++ y
  let k := k.round 10
  -- dbgTrace s!"key: {k.decoded.toList}" λ _ =>
  -- dbgTrace s!"{dump! s.size}" λ _ =>
  let fullSubst := k.fullSubst.toList
  -- dbgTrace s!"{dump! k.subst.map HashSet.toList |>.toList}" λ _ =>
  -- dbgTrace s!"{dump! fullSubst}" λ _ =>
  let x' ← OptionM.run <| x.mapM k.decoded.find?
  let y' ← OptionM.run <| y.mapM k.decoded.find?
  (#[],y')
  -- #eval counts.toList
  -- #eval decode "abcdefg"

def decode₃ (s : Array (Array String)) :
    Option Nat :=
OptionM.run do
  let (_, x) ← decode₂ s
  let x := String.intercalate "" <| x.map toString |>.toList
  String.toNat? x

def examples₀ :=
"acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb ab | cdfeb fcadb cdfeb cdbaf"

def examples₁ :=
"be cfbegad cbdgef fgaecd cgeb fdcge agebfd fecdb fabcd edb | fdgacbe cefdb cefbgd gcbe
edbfga begcd cbg gc gcadebf fbgde acbgfd abcde gfcbed gfec | fcgedb cgb dgebacf gc
fgaebd cg bdaec gdafb agbcfd gdcbef bgcad gfac gcb cdgabef | cg cg fdcagb cbg
fbegcd cbd adcefb dageb afcb bc aefdc ecdab fgdeca fcdbega | efabcd cedba gadfec cb
aecbfdg fbg gf bafeg dbefa fcge gcbea fcaegb dgceab fcbdga | gecf egdcabf bgf bfgea
fgeab ca afcebg bdacfeg cfaedg gcfdb baec bfadeg bafgc acf | gebdcfa ecba ca fadegcb
dbcfg fgd bdegcaf fgec aegbdf ecdfab fbedc dacgb gdcebf gf | cefg dcbef fcge gbcadfe
bdfegc cbegaf gecbf dfcage bdacg ed bedf ced adcbefg gebcd | ed bcgafe cdgba cbgef
egadfb cdbfeg cegd fecab cgb gbdefca cg fgcdab egfdb bfceg | gbdfcae bgc cg cgb
gcafb gcf dcaebfg ecagb gf abcdeg gaef cafbge fdbac fegbdc | fgae cfgab fg bagce"

def inputFileName := "advent/Day8_input.txt"

-- #eval checkInput "Day8" inputFileName

def parseInput (lines : Array String) : IO (Array (Array (Array String))) :=
pure <| lines.map λ ln =>
  String.splitOn ln " | " |>.toArray
  |>.map λ sec => String.splitOn sec " " |>.toArray

def main : IO Unit := do
let ar ← parseInput <| (← IO.FS.lines inputFileName)
-- let ar ← parseInput <| (← lines examples₀)
-- let ar ← parseInput <| (← lines examples₁)
let some decoded ← OptionM.run <| ar.mapM decode₃
  | throw <| IO.userError "parse error"
let output : Nat := Foldable.sum decoded
    -- Foldable.sum <| decoded.map (λ ln => ln.get! 1 |>.size)

IO.println output
-- IO.println "***"
-- for ln in decoded do
  -- IO.println ln

def main₀ : IO Unit := do
-- let ar ← parseInput <| (← IO.FS.lines inputFileName)
let ar ← parseInput <| (← lines examples₁)
let decoded := ar.map (. |>.map (. |>.mapMaybe decode))
let output : Nat :=
    Foldable.sum <| decoded.map (λ ln => ln.get! 1 |>.size)

IO.println output
IO.println "***"
for ln in decoded do
  IO.println ln

#eval main

end Day8
