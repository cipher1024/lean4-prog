
import Lib.Data.AssocList
import Lib.Data.Sorting
import Lib.Data.These
import Lib.Order.Basic

open Std

namespace Option
open These

def mergeWith (f : These α β → Option γ) :
  Option α → Option β → Option γ
| none, none => none
| some x, none => f <| inl x
| none, some y => f <| inr y
| some x, some y => f <| both x y

end Option


namespace Std.AssocList

section defs

variable [Ord k]
variable (f : k → These α β → Option γ)
-- #check Std.AssocList.m
open Nat
-- @[simp]
-- theorem lt_succ_succ (x : Nat) :
--   x < succ (succ x) :=
-- by trans succ x <;> auto

open These AssocList

@[specialize]
def zipWith : AssocList k α → AssocList k β → AssocList k γ
| AssocList.nil, xs =>
  xs.mapFilter <| (f . ∘ inr)
| xs, AssocList.nil =>
  xs.mapFilter <| (f . ∘ inl)
| AssocList.cons i x xs, AssocList.cons j y ys =>
  match compare i j with
  | Ordering.lt =>
    let zs := zipWith xs (cons j y ys)
    match f i <| inl x with
    | none => zs
    | some x' => cons i x' zs
      -- <|
  | Ordering.eq =>
    let zs := zipWith xs ys
    match f i <| both x y with
    | none => zs
    | some x' => cons i x' zs
  | Ordering.gt =>
    let zs := zipWith (AssocList.cons i x xs) ys
    match f i <| inr y with
    | none => zs
    | some x' => cons j x' zs
termination_by zipWith x y => (x.length, y.length)
-- #find prefix getEqn
-- #eval Lean.Meta.getEqnsFor? ``zipWith

-- -- #check Substring
-- variable (xs ys : AssocList k _)
-- open AssocList
-- @[simp]
-- theorem addAux_nil₀ :
--   zipWith f nil ys =
--   ys.mapVal (f ∘ inr) := by
-- cases ys <;>
-- exact WellFounded.fix_eq _ _ _

-- @[simp]
-- theorem addAux_nil₁ :
--   zipWith f xs nil =
--   xs.mapVal (f ∘ inl) := by
-- cases xs <;>
-- exact WellFounded.fix_eq _ _ _

-- @[simp]
-- theorem addAux_cons i x j y :
--   zipWith f (cons i x xs) (cons j y ys) =
--   match compare i j with
--   | Ordering.lt =>
--     cons i (f <| inl x) <| zipWith f xs (cons j y ys)
--   | Ordering.eq =>
--     cons i (f <| both x y) <| zipWith f xs ys
--   | Ordering.gt =>
--     cons j (f <| inr y) <| zipWith f (cons i x xs) ys
--   := WellFounded.fix_eq _ _ _

end defs

-- def R : Nat × α → Nat × α → Prop := (InvImage (.<.) Prod.fst)
open List

-- @[simp]
-- theorem Sorted_map_map :
--   Sorted2 R (List.map (Prod.map id fy) ys) ↔
--   Sorted2 R ys := sorry

-- @[simp]
-- theorem All_LT_map_map :
--   All (R (i, fy x)) (List.map (Prod.map id fy) ys) ↔
--   All (R (i, x)) ys := sorry

variable [LE k] [DecidableTotalOrder k]
variable (f : k → These α β → Option γ)

open List Std.AssocList
-- #check @zipWith

@[auto]
theorem Sublist_keys_mapFilter {xs : AssocList α β}
        {f : α → β → Option γ}:
  Sublist (xs.mapFilter f |>.keys) xs.keys := by
induction xs <;> simp [mapFilter, keys]
. constructor
split
<;> simp [keys]
<;> constructor <;> assumption

theorem All_LT_zipWith (i : k) :
        -- {xs ys : AssocList k α}
        (xs : AssocList k α) →
        (ys : AssocList k β) →
        (Hxs : All (i < .) xs.keys) →
        (Hys : All (i < .) ys.keys) →
  All (i < .) (zipWith f xs ys).keys
| nil, xs, Hxs, Hys => by
  simp [zipWith]
  apply All_of_All_of_Sublist _ Hys
  auto
| xs, nil, Hxs, Hys => by
  cases xs <;> simp [zipWith]
  <;> apply All_of_All_of_Sublist _ Hxs
  <;> auto
| cons i x xs, cons j y ys, Hxs, Hys => by
  simp [zipWith, keys] at Hxs Hys ⊢
  cases Hxs; cases Hys
  next Hxs Hxs' Hys Hys' =>
  split <;>
  next h =>
    simp at h
    split  <;>
    next h' =>
      repeat
        simp [keys]
        first
        | constructor
        | auto
        | apply All_LT_zipWith
termination_by All_LT_zipWith x y _ _ => (x.length, y.length)

theorem Sorted_zipWith (f : k → These α β → Option γ) :
        {xs ys : AssocList k _} →
        (Hxs : Sorted2 (.<.) xs.keys) →
        (Hys : Sorted2 (.<.) ys.keys) →
  Sorted2 (.<.) (zipWith f xs ys).keys
| nil, xs, Hxs, Hys => by
  simp [keys, zipWith]
  apply Sorted2_of_Sorted2_of_Sublist _ Hys
  apply Sublist_keys_mapFilter
| xs, nil, Hxs, Hys => by
  cases xs
  <;> simp [keys, zipWith]
  <;> apply Sorted2_of_Sorted2_of_Sublist _ Hxs
  . constructor
  . apply Sublist_keys_mapFilter
| cons i x xs, cons j y ys, Hxs, Hys => by
  simp [zipWith, keys] at Hxs Hys ⊢
  cases Hxs; cases Hys
  next Hxs Hxs' Hys Hys' =>
  split <;>
  next h =>
    simp at h
    first
    | have h'' := Preorder.le_of_lt h
    | have h'' := Preorder.le_of_eq h
    | have h'' := True.intro
    split <;>
    next h' =>
      repeat
        try simp [keys]
        first
        | constructor
        | auto
        | apply Sorted_zipWith
        | apply All_LT_zipWith
        | apply All_LT_of_lt_of_All_LT h''
      skip
termination_by Sorted_zipWith x y _ _ => (x.length, y.length)

end Std.AssocList

open List
structure OrdMap (α : Type u) [LT α] (β : Type v) where
  vals : AssocList α β
  sorted : Sorted2 (.<.) vals.keys

namespace OrdMap

section defs

variable {k} [LT k]

def empty : OrdMap k α where
  vals := AssocList.nil
  sorted := by constructor

def singleton (x : k) (v : α) : OrdMap k α where
  vals := AssocList.cons x v AssocList.nil
  sorted := by repeat constructor

end defs

section OpWith

open Std.AssocList These

variable [LE k] [DecidableTotalOrder k]
variable (f : k → α → α → α)
variable (g : k → These α β → Option γ)

@[specialize]
def mergeWith (x : OrdMap k α) (y : OrdMap k β) : OrdMap k γ where
  vals := x.vals.zipWith g y.vals
  sorted := Sorted_zipWith _ x.sorted y.sorted

def unionWith :=
mergeWith (λ a => λ
         | inl x => some x
         | both x y => some <| f a x y
         | inr x => some x)

def union : OrdMap k α → OrdMap k α → OrdMap k α :=
unionWith (λ a x _ => x)

variable (f : k → α → β → γ)

def intersectionWith :=
mergeWith (λ a => λ
         | inl x => none
         | both x y => some <| f a x y
         | inr x => none)

def intersection : OrdMap k α → OrdMap k α → OrdMap k α :=
intersectionWith (λ a x _ => x)

def difference : OrdMap k α → OrdMap k β → OrdMap k α :=
mergeWith (λ a => λ
         | inl x => some x
         | both x y => none
         | inr x => none)

def insert (x : k) (v : α) : OrdMap k α → OrdMap k α :=
union (singleton x v)

def erase (x : k) : OrdMap k α → OrdMap k α :=
λ m => difference m (singleton x ())

end OpWith

section misc
variable [LT k]

def foldl (f : β → k → α → β) (x₀ : β) (m : OrdMap k α) : β :=
m.vals.foldl f x₀

variable [BEq k]

def find? (x : k) (m : OrdMap k α) : Option α :=
m.vals.find? x

end misc

section thms
variable [LE k] [DecidableTotalOrder k]

variable (x y : OrdMap k α)
-- variable


theorem ext
        (h : ∀ i, x.find? i = y.find? i) :
  x = y := sorry

variable (y : OrdMap k β)

@[simp]
theorem find?_merge (f : k → These α β → Option γ) :
  (mergeWith f x y).find? i =
  Option.mergeWith (f i) (x.find? i) (y.find? i) :=
sorry

@[simp]
theorem find?_empty (i : k) : empty.find? i = @none α := sorry

-- @[simp]
-- theorem find?_singleton (i : k) : empty.find? i = @none α := sorry

end thms

end OrdMap
