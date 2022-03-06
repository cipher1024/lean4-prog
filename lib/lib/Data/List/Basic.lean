
import Lib.Tactic

namespace List

instance : Functor List where
  map := List.map

variable {α β} (xs ys : List α) (f : β → α → β) (x₀ : β)

@[simp]
theorem foldl_app :
  foldl f x₀ (xs ++ ys) = foldl f (foldl f x₀ xs) ys := by
induction xs generalizing x₀ <;> auto

theorem foldl_eq_self :
  (xs.foldl (flip (.::.)) []).reverse = xs := by
simp only [flip]
trans (List.reverse [] ++ xs)
case second => simp
generalize [] = ys
induction xs generalizing ys
 <;> simp [List.foldl, *, List.append_assoc]

theorem foldr_eq_self :
  (xs.foldr (.::.) []) = xs := by
trans (xs ++ [])
case second => simp
generalize [] = ys
induction xs generalizing ys
 <;> simp [List.foldr, *, List.append_assoc]


@[simp]
theorem map_nil (f : α → β) : f <$> [] = [] := rfl

@[simp]
theorem map_cons (f : α → β) x xs :
  f <$> (x :: xs) = f x :: f <$> xs := rfl

@[simp]
theorem redLength_eq (xs : List α) :
  redLength xs = length xs := by
induction xs <;> simp [redLength, *]

@[simp]
theorem length_map {f : α → β} (xs : List α) :
  length (f <$> xs) = length xs := by
simp [(.<$>.)]
induction xs <;> simp [length, *]

@[simp]
theorem take_zero (xs : List α) : xs.take 0 = [] := by
induction xs <;> simp [take]

@[simp]
theorem drop_zero (xs : List α) : xs.drop 0 = xs := by
induction xs <;> simp [drop]

@[simp]
theorem drop_nil n : (@nil α).drop n = [] := by
cases n <;> refl

theorem cons_drop {i} {xs : List α} (h : i < length xs) :
  get xs ⟨i, h⟩ :: drop i.succ xs = drop i xs := by
induction xs generalizing i;
. cases h
cases i <;> simp [get, drop, *] at h ⊢

@[simp]
theorem take_length (xs : List α) : xs.take xs.length = xs := by
induction xs <;> simp [take, length, *]

@[simp]
theorem drop_length (xs : List α) : xs.drop xs.length = [] := by
induction xs <;> simp [drop, *]

@[simp]
theorem length_eq_zero (xs : List α) :
  xs.length = 0 ↔ xs = [] := by
cases xs <;> simp [length, Nat.add_one]

@[simp]
theorem foldl_reverse (xs : List α) (f : β → α → β) :
  xs.reverse.foldl f x₀ = xs.foldr (flip f) x₀ := by
induction xs <;> simp [foldl, foldr, *]; refl

end List

namespace List

variable {α β γ : Type _} {f : β → α → β} {g : γ → α → γ}
variable {SIM : β → γ → Prop}
variable {x₀ y₀} (t : List α)

theorem foldl_sim :
    SIM x₀ y₀ →
    (∀ a x y, SIM x y → SIM (f x a) (g y a)) →
    SIM (foldl f x₀ t) (foldl g y₀ t) := by
induction t generalizing x₀ y₀ <;> auto

end List
