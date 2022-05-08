
import Lib.Data.Foldable
import Lib.Data.Nat
import Lib.Order.Basic
import Lib.Logic.Basic
import Lib.Logic.Classical
import Lib.Data.Fold
import Lib.Data.List.Instances
-- #check Nat.divides
-- def Divides

namespace List
open LawfulFoldable

def iota_of_pos (h : p > 0) :
  iota p = p :: iota (p - 1) := by
cases p
. cases h
. refl

@[simp]
theorem product_nil [Monoid α] (p : α) :
  Foldable.product (@nil α) = 1 :=
by simp [product_eq_foldr, Foldable.foldr, foldr]

@[simp]
theorem product_cons [Monoid α] (p : α) :
  Foldable.product (p :: ps) = p * Foldable.product ps :=
by simp [product_eq_foldr, Foldable.foldr, foldr]

end List

namespace Nat

@[auto]
theorem lt_add {x y : Nat} (h : 0 < y) :
  x < x + y := by
apply Nat.lt_of_le_of_lt (m := x + 0)
. rw [Nat.add_zero]; refl
. auto [Nat.add_lt_add_left]

theorem divides_refl : p ∣ p := by
refine' ⟨1, _⟩; rw [Nat.mul_one]

instance : Reflexive divides where
  refl p := divides_refl

theorem divides_trans (hpq : p ∣ q) (hqr : q ∣ r) :
  p ∣ r := by
cases hpq with | intro x hpq =>
cases hqr with | intro y hqr =>
exists x * y
rw [← Nat.mul_assoc, hpq, hqr]

instance : Trans divides divides divides where
  trans := divides_trans

theorem divides_sub
        (hp : x ∣ p) (hq : x ∣ q) :
  x ∣ (p - q) := by
cases hp with | intro xp hp =>
cases hq with | intro xq hq =>
exists (xp - xq)
rw [Nat.mul_sub_left_distrib, hp, hq]

theorem divides_add
        (hp : x ∣ p) (hp' : x ∣ (p + q)) :
  x ∣ q := by
have := divides_sub hp' hp
rw [Nat.add_sub_cancel_left] at this
exact this

-- cases this with | intro y hp =>
-- suffices h : y = 1
--   by rw [h, Nat.mul_one] at hp; assumption
-- admit
-- -- apply Nat.le_antisymm
-- next =>
--   rw [← hp]
--   trans (x * 1); rw [Nat.mul_one]; refl
--   apply Nat.mul_le_mul_left
--   cases y
--   . rw [Nat.mul_zero] at hp; cases hp
--   . auto
-- next =>
--   rw [← hp]
--   trans (x * 1) </> auto
--   -- apply Nat.le_mul


theorem divides_mul
        (hp : x ∣ q) :
  x ∣ p * q := by
cases hp with | intro xq hq =>
exists xq * p
rw [← Nat.mul_assoc, hq, Nat.mul_comm]

theorem le_of_divides
        (hp : p ∣ q) (hq : q > 0) :
  p ≤ q := by
cases hp with | intro z hp =>
suffices hz : p * 1 ≤ p * z by
  rw [hp, Nat.mul_one] at hz; assumption
apply Nat.mul_le_mul_left
cases z
. rw [Nat.mul_zero] at hp; subst hp; cases hq
. auto

theorem one_le_product {xs : List Nat}
        (h : ∀ x, x ∈ xs → 1 ≤ x) :
  1 ≤ Foldable.product xs := by
induction xs <;> simp
next x xs ih =>
  suffices 1 * 1 ≤ x * Foldable.product xs
    by rw [Nat.mul_one] at this; assumption
  apply Nat.mul_le_mul
  . apply h; constructor
  . apply ih; intros y Hy; auto

end Nat

namespace Nat

-- #check Fold.product

def IsPrime (p : Nat) : Prop :=
1 < p ∧
∀ q, 1 < q → q < p → ¬ Nat.divides q p

-- set_option trace.Meta.Tactic.simp.rewrite true

-- attribute [local simp]

theorem divides_implies_exists_primes (hp : p > 1) :
  ∃ p', p' ∣ p ∧ IsPrime p' := by
induction p using Nat.strong_ind
next p ih =>
by_cases h' : IsPrime p
next =>
  refine' ⟨_, _, h'⟩
  apply divides_refl
next =>
  simp [IsPrime, -Classical.not_and, Classical.not_and_iff_implies] at h'
  specialize h' hp
  match h' with
  | ⟨p', h₀, h₁, h₂⟩ =>
    specialize ih _ h₁ h₀
    match ih with
    | ⟨p'', h₄, h₅⟩ =>
      have := divides_trans h₄ h₂
      constructor <;> auto

theorem divides_product (xs : List Nat)
        (h : x ∈ xs) :
  x ∣ Foldable.product xs := by
induction xs
next => cases h
next y ys ih =>
  cases h <;> rw [List.product_cons]
  next =>
    refine ⟨_, rfl⟩
  next h =>
    specialize ih h
    auto [divides_mul]

section
open Classical

noncomputable
def primes_upto (p : Nat) : List Nat :=
List.iota p |>.filter λ p => IsPrime p

theorem primes_upto_of_pos (h : p > 0) (h' : IsPrime p) :
  primes_upto p = p :: primes_upto (p - 1) := by
simp [primes_upto]; rw [List.iota_of_pos h]
simp [*]

noncomputable
def bigger_prime (p : Nat) : Nat :=
Foldable.product <| primes_upto p

end

-- set_option pp.proofs.withType false
-- set_option pp.analyze.typeAscriptions true
-- set_option pp.all true

-- #check Classical.not_forall
-- #check List.filter_cons_false
-- set_option trace.Meta.Tactic.simp.rewrite true
theorem infinite_primes p :
  ∃ q, p < q ∧ IsPrime q := by
let z := bigger_prime p + 1
have hz : 1 < z := by
  suffices hz : 0 + 1 < bigger_prime p + 1
    by rw [Nat.zero_add] at hz; assumption
  apply Nat.add_lt_add_right
  apply one_le_product; simp [primes_upto]; auto
have ⟨p', hz, hprime⟩ := divides_implies_exists_primes hz
suffices hz' : p < p' from ⟨_, hz', hprime⟩
byContradiction h; next h =>
simp at h
have hh : 1 < p' := hprime.1
have : p' ∈ primes_upto p :=
  by simp [primes_upto]; auto
have : p' ∣ Foldable.product (primes_upto p) :=
  divides_product _ this
have := divides_add this hz
have := le_of_divides this (by auto)
have hh := Nat.not_le_of_gt hh
contradiction

section minimum
open Classical
variable {p : Nat → Prop}
variable (hp : ∃ x, p x)

theorem minimum_exists :
  ∃ x, p x ∧ ∀ y, y < x → ¬ p y := by
cases hp with | intro x hp =>
induction x using Nat.strong_ind
next x ih =>
  negate_goal h; simp [- not_and, not_and_iff_implies] at h
  specialize h _ hp
  match h with
  | ⟨y, hyx, hpx⟩ => eauto

noncomputable
def minimum :=
Classical.choose (minimum_exists hp)

theorem minimum_satisfies :
  p (minimum hp) :=
Classical.choose_spec (minimum_exists hp) |>.1

theorem minimum_le (hx : p x) :
  minimum hp ≤ x := by
negate_goal h'; simp at h'
have h := Classical.choose_spec (minimum_exists hp) |>.2 _ h'
contradiction

end minimum

noncomputable
def next_prime p :=
minimum (infinite_primes p)

theorem IsPrime_next_prime p :
  IsPrime (next_prime p) :=
minimum_satisfies (infinite_primes p) |>.2

-- theorem

-- def minimum ()

-- by_cases hz : IsPrime z
-- next =>
--   suffices hz' : p < z from ⟨_, hz', hz⟩
--   have hp : 0 < p := sorry
--   apply Nat.lt_of_le_of_lt (m := bigger_prime p)
--   next =>
--     simp [bigger_prime, primes_upto_of_pos hp h]
--     suffices h : p * 1 ≤ p * Foldable.product (primes_upto (p - 1))
--       by rw [Nat.mul_one] at h; exact h
--     apply mul_le_mul_left
--     admit
--   next => auto
-- next =>
--   simp [IsPrime] at hz
--   match hz with
--   | ⟨x,hx₀,hx₁,hdvd⟩ =>
--     skip
 -- apply lt_add
    -- apply le_mul
  -- refine
-- apply not_not


end Nat
