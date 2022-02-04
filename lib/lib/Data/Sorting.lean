
import Lib.Tactic
import Std.Data.AssocList

namespace List

inductive All (P : α → Prop) : List α → Prop where
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

attribute [auto] All.nil All.cons

inductive Sorted (R : α → α → Prop) : List α → Prop where
  | nil : Sorted R []
  | single : Sorted R [x]
  | cons1 {x x'} {xs} :
    R x x' →
    Sorted R (x' :: xs) →
    Sorted R (x :: x' :: xs)

inductive Sorted2 (R : α → α → Prop) : List α → Prop where
  | nil : Sorted2 R []
  | cons {x xs} :
    All (R x) xs →
    Sorted2 R xs →
    Sorted2 R (x :: xs)

attribute [auto] Sorted2.nil Sorted2.cons

inductive Sublist : (xs ys : List α) → Prop where
  | nil {xs} : Sublist [] xs
  | cons {x xs xs'} :
    Sublist xs xs' →
    Sublist (x :: xs) (x :: xs')
  | drop {x xs xs'} :
    Sublist xs xs' →
    Sublist xs (x :: xs')

attribute [auto] Sublist.nil Sublist.cons Sublist.drop

variable {xs ys : List α} {P : α → Prop}

theorem All_of_All_of_Sublist
        (h₀ : Sublist xs ys)
        (h₁ : All P ys) :
  All P xs := by
induction h₀ <;>
repeat
  first
  | auto
  | cases h₁

variable {R : α → α → Prop}

theorem Sorted2_of_Sorted2_of_Sublist
        (h₀ : Sublist xs ys)
        (h₁ : Sorted2 R ys) :
  Sorted2 R xs := by
induction h₀ <;>
repeat
  first
  | auto
  | cases h₁
constructor </> auto
apply All_of_All_of_Sublist
<;> assumption

end List
