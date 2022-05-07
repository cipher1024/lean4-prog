
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

/-- drop -/

theorem drop_append' {xs ys : List α}
        (h : xs.length = n) :
  (xs ++ ys).drop n = ys := by
induction xs generalizing n with
| nil =>
  cases n <;> simp
  cases h
| cons x xs ih =>
  cases n <;> simp only [drop, List.cons_append]
  <;> cases h
  auto

theorem drop_append {xs ys : List α} :
  (xs ++ ys).drop xs.length = ys :=
drop_append' rfl

/- mem -/

section mem

attribute [auto] List.Mem

@[simp]
theorem mem_nil : ¬ x ∈ @nil α := by
intro h; cases h

@[simp]
theorem mem_cons {ys : List α} : x ∈ y :: ys ↔ x = y ∨ x ∈ ys := by
constructor
next =>
  intro h; cases h
  . left; refl
  . right; assumption
next =>
  intro h; cases h;
  next h =>
    subst h; auto
  next => auto

end mem

/- filter -/

section filter

variable {p : α → Bool}
variable {x : α} {xs : List α}

theorem filterAux_eq :
  filterAux p xs ys = reverse ys ++ filterAux p xs [] := by
induction xs generalizing ys
next => simp [filterAux]
next x xs ih =>
  simp [filterAux]; split
  <;> simp [ih (x :: ys), ih [x], append_assoc]
  auto

theorem filter_cons_eq_ite :
  filter p (x :: xs) =
  ite (p x)
    (x :: filter p xs)
    (filter p xs) := by
simp [filter, filterAux]; split <;> simp [*]
rw [filterAux_eq]; simp

@[simp]
theorem filter_nil {p : α → Bool} :
  filter p [] = [] :=
by simp [filter, filterAux]

@[simp]
theorem filter_cons_true {p : α → Bool} {x xs}
        (h : p x = true) :
  filter p (x :: xs) = x :: filter p xs :=
by simp [filter_cons_eq_ite, *]

@[simp]
theorem filter_cons_false {p : α → Bool} {x xs}
        (h : p x = false) :
  filter p (x :: xs) = filter p xs :=
by simp [filter_cons_eq_ite, *]

attribute [local auto] Or

@[simp]
theorem mem_filter {p : α → Bool} :
  x ∈ filter p xs ↔ x ∈ xs ∧ p x := by
induction xs
next => simp
next y ys ih =>
  by_cases p y <;> simp [*]
  next =>
    constructor <;> intro h
    next =>
      cases h
      next => substAll; auto
      next h => auto
    next =>
      match h with
      | ⟨.inl h, h'⟩ =>
        subst h; left; refl
      | ⟨.inr h, h'⟩ =>
        right; auto
  next =>
    constructor <;> intro h
    next => auto
    next =>
      match h with
      | ⟨.inl h, h'⟩ =>
        substAll; auto
      | ⟨.inr h, h'⟩ =>
        auto

end filter

/- iota -/

section iota

@[simp]
theorem mem_iota :
  x ∈ iota n ↔ 1 ≤ x ∧ x ≤ n := by
induction n <;> simp [iota, *]
next =>
  intros h; cases h
  next h₀ h₁ => subst h₁; cases h₀
next =>
  admit -- linear arithmetic
  -- constructor <;> intro h
  -- skip

end iota

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
