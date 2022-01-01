
import Sat.Tactics

namespace List

variable {α β} (xs ys : List α) (f : β → α → β) (x₀ : β)

@[simp]
theorem foldl_app :
  foldl f x₀ (xs ++ ys) = foldl f (foldl f x₀ xs) ys := by
induction xs generalizing x₀ <;> auto

theorem append_cons (xs : List α) (y ys) :
  xs ++ y :: ys = (xs ++ [y]) ++ ys := by
induction xs <;> simp [*]

theorem foldl_eq_self :
  (xs.foldl (flip (.::.)) []).reverse = xs := by
simp only [flip]
trans (List.reverse [] ++ xs)
case second => simp
generalize [] = ys
induction xs generalizing ys
 <;> simp [List.foldl, *, List.append_assoc]

end List
