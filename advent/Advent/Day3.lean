
def readBinNum? (s : String) : IO (Array Nat) :=
  if s.isNat then
    pure <| s.foldl (fun n c => n.push (c.toNat - '0'.toNat)) (Array.mkEmpty 5)
  else
    throw <| IO.userError "bad number"

def examples :=
"00100
11110
10110
10111
10101
01111
00111
11100
10000
11001
00010
01010"

def String.lines (s : String) : Array String :=
(s.splitOn "\n").toArray

def Array.grow (ar : Array α) (sz : Nat) (x : α) : Array α :=
if ar.size < sz then
  let suff := Array.mkArray (sz - ar.size) x
  ar ++ suff
else ar

def countOneBit : (acc : Nat × Nat) → (num : Nat) → Nat × Nat
| ⟨b0, b1⟩, b =>
  if b == 0 then ⟨b0+1, b1⟩
  else ⟨b0, b1+1⟩

def countBits (acc : Array (Nat × Nat)) (num : Array Nat) : Array (Nat × Nat) :=
let acc := acc.grow num.size (0, 0)
acc.zipWith num countOneBit

def countNthBits (n : Nat) (acc : Nat × Nat) (num : Array Nat) : Nat × Nat :=
countOneBit acc (num.get! n)

def majority (counts : Array (Nat × Nat)) : Array Nat :=
counts.map λ ⟨b0,b1⟩ =>
  if b0 < b1 then 1
  else 0

def minority (counts : Array (Nat × Nat)) : Array Nat :=
counts.map λ ⟨b0,b1⟩ =>
  if b0 < b1 then 0
  else 1

def toDecimal (num : Array Nat) : Nat :=
num.foldl (λ acc d => acc*2 + d) 0

-- Part1
def decodeRates (input : Array (Array Nat)) : Nat :=
let count := input.foldl countBits (Array.mkEmpty 10)
let gammaRate := toDecimal $ majority count
let epsilonRate := toDecimal $ minority count
(gammaRate * epsilonRate)

-- Part 2
def airRatesFilter (n : Nat) (keepMostCommon : Bool)
    (input : Array (Array Nat)) : Array (Array Nat) :=
let ⟨count0, count1⟩ := input.foldl (countNthBits n) (0, 0)
let selected :=
    if keepMostCommon then
       if count0 > count1 then 0 else 1
    else
       if count0 > count1 then 1 else 0
input.filter λ a => a.get! n == selected

partial def iterateAirRatesFilter (n : Nat) (keepMostCommon : Bool)
            (input : Array (Array Nat)) : Array Nat :=
  if input.size ≤ 1 then input.get! 0
  else iterateAirRatesFilter (n+1) keepMostCommon
                             (airRatesFilter n keepMostCommon input)

def decodeAirRates (input : Array (Array Nat)) : Nat × Nat × Nat :=
  let O₂Rate := toDecimal $ iterateAirRatesFilter 0 true input
  let CO₂Rate := toDecimal $ iterateAirRatesFilter 0 false input
  (O₂Rate, CO₂Rate, O₂Rate * CO₂Rate)

namespace Day3

def inputFileName := "Advent/Day3_input.txt"

def main : IO Unit := do
  let lns ← (← IO.FS.lines inputFileName).mapM readBinNum?
  IO.println $ decodeRates lns
  IO.println $ decodeAirRates lns

#eval main

end Day3
