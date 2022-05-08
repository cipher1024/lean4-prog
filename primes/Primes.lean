
import Lib.Data.Array
import Lib.Data.Nat
import Lib.Data.DecSubtype
import Lib.Data.OrdMap
import Lib.Logic.Classical

namespace Nat

theorem lt_mul_iff_div_lt {x y k : Nat} (h : 1 ≤ k) :
  x < y*k ↔ x / k < y := by
rw [← Classical.not_iff_not, ← le_iff_not_lt, mul_le_iff_le_div, le_iff_not_lt]
 <;> auto

end Nat

inductive InfArrayBuf (α : Type u) : Nat → Type u where
  | default : α → n > 0 → InfArrayBuf α n
  | node : Buffer n α → InfArrayBuf α (n*2) → InfArrayBuf α n

namespace InfArrayBuf

theorem is_pos (ar : InfArrayBuf α n) : n > 0 := by
induction ar with
| default x h => exact h
| node buf ar ih =>
  simp [Nat.lt_mul_iff_div_lt] at ih
  auto

def mk (x : α) (h : n > 0) : InfArrayBuf α n :=
default x h

def get : InfArrayBuf α n → Nat → α
| default x _, _ => x
| ar@(node buf ar'), i =>
  if h : i < n then
    buf.get ⟨i, h⟩
  else
    get ar' (i - n)
def set : InfArrayBuf α n → Nat → α → InfArrayBuf α n
| default x h, i, y =>
  let buf := Buffer.mkFilled x
  have h'' : n*2 > 0 := by
    simp [Nat.lt_mul_iff_div_lt]; auto
  if h' : i < n then
    node (buf.set ⟨i, h'⟩ y) (default x h'')
  else
    have h₂ : 0 < i := Nat.lt_of_lt_of_le h (Nat.le_of_not_gt h')
    have h₃ : i - n < i := Nat.sub_lt h₂ h
    node buf (set (default x h'') (i - n) y)
| ar@(node buf ar'), i, x =>
  if h' : i < n then
    node (buf.set ⟨i, h'⟩ x) ar'
  else
    have h'' : n*2 > 0 := ar'.is_pos
    have h   : n > 0 := ar.is_pos
    have h₂ : 0 < i := Nat.lt_of_lt_of_le h (Nat.le_of_not_gt h')
    have h₃ : i - n < i := Nat.sub_lt h₂ h
    node buf (set ar' (i - n) x)
termination_by _ i _ => i

def size : InfArrayBuf α n → Nat
| default _ _ => 0
| node _ ar => n + ar.size

def toList : InfArrayBuf α n → Nat → List α
| default x h, n => List.replicate n x
| node buf ar, m =>
  if m ≤ n then buf.cells.toList.take m
  else buf.cells.foldr (. :: .) (toList ar (m - n))

def dropHead : InfArrayBuf α n → InfArrayBuf α (n*2)
| default x h => default x <| by simp [Nat.lt_mul_iff_div_lt]; auto
| node buf ar => ar

end InfArrayBuf

structure InfArray (α : Type u) where
mkImpl ::
  bufSize : Nat
  buffers : InfArrayBuf α bufSize

namespace InfArray

def mkFilled (x : α) : InfArray α where
  bufSize := 10
  buffers := InfArrayBuf.node (Buffer.mkFilled x)
    (InfArrayBuf.default x <| by auto)

def size (ar : InfArray α) : Nat :=
ar.buffers.size

def get (ar : InfArray α) (i : Nat) : α :=
ar.buffers.get i

def set (ar : InfArray α) (i : Nat) (x : α) : InfArray α where
  buffers := ar.buffers.set i x

def toList (ar : InfArray α) (n : Nat) : List α :=
ar.buffers.toList n

def dropHead (ar : InfArray α) : InfArray α where
  buffers := ar.buffers.dropHead

end InfArray

def Heap := OrdMap

namespace Heap
open Std.AssocList
variable [LT α]

def takeMin (h : Heap α β) : Option (α × β × Heap α β) :=
match h' : h.vals with
| nil => none
| cons k v xs =>
  let xs' :=
    { vals := xs
      sorted := by
        have h'' := h.sorted
        simp [h', keys] at h''
        cases h''; assumption }
  -- let z := h.insert
  some (k, v, xs')

def nonEmpty (h : Heap α β) : Bool :=
match h.vals with
| nil => false
| cons k v xs => true

def empty : Heap α β where
  vals := nil
  sorted := by constructor

end Heap

def NEHeap (α) [LT α] (β) :=
DecSubtype (Heap.nonEmpty (α := α) (β := β))

namespace NEHeap
open Std.AssocList
variable [LT α]

def takeMin (h : NEHeap α β) : α × β × Heap α β :=
match h' : h with
| ⟨ ⟨cons k v xs, hxs ⟩, rfl ⟩ =>
  let xs' :=
    { vals := xs
      sorted := by
        have h'' := h.val.sorted
        simp [h', keys] at h''
        cases h''; assumption }
  (k, v, xs')

def head (h : NEHeap α β) : α :=
match h' : h with
| ⟨ ⟨cons k v xs, hxs ⟩, rfl ⟩ => k

end NEHeap


namespace OrdMap

variable [LE k] [DecidableTotalOrder k]
variable (f : k → α → α → α)

def insertWith (x : k) (v : α) :
  OrdMap k α → OrdMap k α :=
unionWith f (singleton x v)

end OrdMap


namespace Heap
open Std.AssocList
variable [LE α] [DecidableTotalOrder α]
variable (f : α → β → β → β)

def insertWith' (h : Heap α β) (k : α) (v : β) : NEHeap α β where
  val := h.insertWith f k v
  property := by
    cases h' : h.vals <;>
    simp [OrdMap.insertWith, OrdMap.unionWith, OrdMap.unionWith, OrdMap.mergeWith] <;>
    simp [OrdMap.singleton, h', zipWith, mapFilter, nonEmpty]
    next k v k' v' tail =>
      cases compare k k' <;> simp

end Heap

structure SieveEntry where
mkImpl ::
  key : Nat
  prime : Nat
  coef : Nat
  cached_key : key = prime * coef
  le_coef : prime ≤ coef

instance : ToString SieveEntry where
  toString x := toString (x.prime, x.coef)

namespace SieveEntry

def mk (n : Nat) : SieveEntry where
  key := n * n
  prime := n
  coef := n
  le_coef := Nat.le_refl _
  cached_key := rfl

def step' (s : SieveEntry) : SieveEntry where
  key := s.key + s.prime + s.prime
  prime := s.prime
  coef := s.coef + 2
  le_coef := by trans _; apply s.le_coef; auto
  cached_key := by simp [Nat.mul_succ, s.cached_key]

def step (s : SieveEntry) : Nat × SieveEntry :=
let s' := s.step'
(s'.key, s')

end SieveEntry

def List.nonEmpty : List α → Bool
| [] => false
| _ :: _ => true

def NEList (α) := DecSubtype (List.nonEmpty (α := α))

namespace NEList

def append : NEList α → NEList α → NEList α
| ⟨x :: xs, rfl⟩, ⟨ys, _⟩ => ⟨x :: (xs ++ ys), rfl⟩

instance : Append (NEList α) := ⟨ append ⟩

instance [Repr α] : Repr (NEList α) where
  reprPrec x n := reprPrec x.1 n

instance [ToString α] : ToString (NEList α) where
  toString x := toString x.1

end NEList

structure SieveState where
  cursor : NEHeap Nat (NEList SieveEntry)
  -- offset : Nat
  -- flags : InfArray Bool
  next : Nat
  primes : Array Nat

namespace SieveState

def pushPrime (n : Nat) (h : Heap Nat (NEList SieveEntry)) :
  NEHeap Nat (NEList SieveEntry) :=
let e := SieveEntry.mk n
h.insertWith' (λ _ => (. ++ .)) e.key ⟨ [e], rfl ⟩

-- def toList (s : SieveState) (n : Nat) : List (Nat × Bool) :=
-- s.flags.toList n |>.enumFrom s.offset |>.map <| Prod.map (. *2 +1) id

def init : SieveState where
  cursor := pushPrime 3 Heap.empty
  -- offset := 0
  -- flags := InfArray.mkFilled true
  next := 2 -- we consider only next * 2 + 1
  primes := #[2,3]

def next' (s : SieveState) : Nat := s.next*2 + 1

-- def index (s : SieveState) (c : Nat) : Nat :=
-- (((c - 1) / 2) - s.offset)

def insert (h : Heap Nat (NEList SieveEntry)) (e : SieveEntry) :
  NEHeap Nat (NEList SieveEntry) :=
h.insertWith' (λ _ => (. ++ .)) e.key ⟨[e],rfl⟩

def steps (h : Heap Nat (NEList SieveEntry)) :
  NEList SieveEntry →
  NEHeap Nat (NEList SieveEntry)
| ⟨e::es, rfl⟩ =>
  let (c', e') := e.step
  let h' := insert h e'
  es.foldl (λ h e => insert h.1 e.step') h'
   -- match es with
  -- | [] => h'
  -- | ys@(e' :: es) =>
    -- have : ys.length < xs.length := sorry
    -- steps h'.val ⟨e':: es, rfl ⟩
-- termination_by _ es => es.val.length

def step' (s : SieveState) : SieveState :=
let (c, es, cursor') := s.cursor.takeMin
-- let (c', e') := e.step
-- let i := s.index c
let cursor' := steps cursor' es
-- let flags' := s.flags.set i false
{ cursor := cursor'
  -- offset := s.offset
  -- flags := flags'
  next := s.next
  primes := s.primes
}

-- def condition (s : SieveState) : Bool × Nat × Nat :=
-- ( s.next' < s.cursor.head ∧ s.flags.get (s.index s.next),
--  s.index s.next,
--  s.next
-- )

-- def toList (s : SieveState) : List (Nat × Bool) :=

def step (s : SieveState) : SieveState :=
-- if s.offset + s.flags.bufSize ≤ s.next then
  -- { s with
    -- offset := s.offset + s.flags.bufSize
    -- flags := s.flags.dropHead }
if s.next' < s.cursor.head then
  let p := s.next'
  -- let i := s.next - s.offset
  -- let i := s'.next
  let cursor' := pushPrime p s.cursor.1
  let primes' := s.primes.push p
  { s with
           next := s.next + 1
           cursor := cursor'
           primes := primes' }
else if s.next' = s.cursor.head then
  { s.step' with next := s.next + 1 }
else
  s.step'

def test : IO Unit := do
  let mut s := init
  for i in [0:79] do
    s := step s
  print_vars![s.next', s.primes,
              s.cursor.val.vals.toList]

-- #eval test

end SieveState
