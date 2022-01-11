
namespace Array

variable (f : Nat → β → α → β)

def foldlIdx (x₀ : β) (ar : Array α) : β :=
ar.foldl (λ (i, x) acc => (i+1, f i x acc)) (0, x₀) |>.2

def sum [OfNat α 0] [Add α] : Array α → α :=
foldl (.+.) 0

end Array

namespace Document

namespace Table

def updateWidth [ToString α]
    (i : Nat) (spec : Array Nat) (c : α) : Array Nat :=
let spec :=
  if i ≥ spec.size then
    let size := max (i+1) <| spec.size * 2
    spec ++ Array.mkArray (size - spec.size) 0
  else spec
spec.modify i (max (toString c).length)

def mkColumnSpec [ToString α] (t : List (Array α)) :=
t.foldl (λ acc row => row.foldlIdx updateWidth acc) #[]

inductive Alignment where
  | left
  | right

structure Cell where
  toString : String
  align : Alignment
  -- optional := false

instance : ToString Cell where
  toString c := c.toString

def leftAlign (s : String) : Cell :=
⟨s, Alignment.left⟩

def rightAlign (s : String) : Cell :=
⟨s, Alignment.right⟩

def Cell.format (c : Cell) (w : Nat) : String :=
let padding := (w - c.toString.length).repeat (. ++ " ") ""
match c.align with
| Alignment.left => s!" {c.toString}{padding}"
| Alignment.right => s!" {padding}{c.toString}"

def renderRow (spec : Array Nat) (row : Array Cell) : String :=
String.join
    <| Array.toList
    <| row.mapIdx λ i c =>
      if spec.get! i.1 = 0 then ""
      else
        c.format (spec.get! i.1)

def renderTable (t : List (Array Cell)) : String :=
let spec := mkColumnSpec t
String.intercalate "\n" <| t.map (renderRow spec)

end Table

namespace Paragraph

def wrapParagraph (w : Nat) (ln : String) : List String :=
let rec loop (len : Nat) (ls : List String) (ln : String) : List String :=
  match ls with
  | [] => [ln]
  | l::ls =>
    if l.length + 1 ≤ len then
      loop (len - l.length - 1) ls (ln ++ " " ++ l)
    else
      ln :: loop (w - l.length) ls l
let ls := ln.splitOn " "
match ls with
| [] => [""]
| l :: ls =>
  loop (w - l.length) ls l

end Paragraph

end Document
