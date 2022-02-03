
import Lib.Logic.Basic
import Lib.Data.Nat
import Lib.Meta.DeclGraph
import Lib.Tactic

variable (α : Type u) [LE α]

class Preorder extends LT α, @Reflexive α (.≤.) where
  trans {x y z : α} :
    x ≤ y → y ≤ z → x ≤ z
  lt_iff {x y : α} :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x

namespace Preorder

variable {α} [LE α] [Preorder α] {x y : α}

@[auto]
theorem le_of_eq : x = y → x ≤ y := by
intros h; subst h; auto

theorem lt_irrefl (x : α) : ¬ x < x :=
by rw [lt_iff]; auto

theorem lt_antisymm {x y : α} : x < y → y < x → False :=
by simp [lt_iff]; auto

variable {x y z w : α}

theorem lt_of_le_of_lt_of_le
        (h₀ : x ≤ y)
        (h₁ : y < z)
        (h₂ : z ≤ w) :
  x < w := by
rw [lt_iff] at h₁ ⊢
cases h₁ with | intro h₁ hb =>
constructor
next =>
  repeat
    first
    | assumption
    | apply Preorder.trans
next =>
  intros ha; apply hb; clear hb
  repeat
    first
    | assumption
    | apply Preorder.trans

theorem lt_of_le_of_lt
        (h₀ : x ≤ y)
        (h₁ : y < z) :
  x < z :=
lt_of_le_of_lt_of_le h₀ h₁ (Reflexive.refl _)

theorem lt_of_lt_of_le
        (h₁ : x < y)
        (h₂ : y ≤ z) :
  x < z :=
lt_of_le_of_lt_of_le (Reflexive.refl _) h₁ h₂

end Preorder

class PartialOrder extends Preorder α where
  antisymm {x y : α} : x ≤ y → y ≤ x → x = y

namespace PartialOrder

open Preorder

variable {α} [LE α] [PartialOrder α] {x y : α}

theorem le_iff_lt_or_eq : x ≤ y ↔ x < y ∨ x = y := by
rw [lt_iff]
constructor <;> intros h
next =>
  byCases h : y ≤ x; right
  . auto [antisymm]
  . left; auto
next =>
  cases h <;> auto

@[auto]
theorem le_of_lt : x < y → x ≤ y :=
by rw [lt_iff]; auto

end PartialOrder


class TotalOrder extends PartialOrder α where
  total (x y : α) : x ≤ y ∨ y ≤ x

namespace TotalOrder

open Preorder PartialOrder

variable {α} [LE α] [TotalOrder α] (x y : α)

@[simp]
theorem not_le : ¬ x ≤ y ↔ y < x := by
rw [lt_iff]
constructor <;> intros h
next =>
  cases total x y <;> auto
next =>
  auto

@[simp]
theorem not_lt : ¬ x < y ↔ y ≤ x := by
rw [lt_iff]
constructor <;> intros h
next =>
  byContradiction h
  cases total x y <;> auto
next =>
  auto

theorem trichonomy : x < y ∨ x = y ∨ y < x := by
cases total x y
next h =>
  rw [le_iff_lt_or_eq] at h
  cases h
  . left; assumption
  . right; left; assumption
next h =>
  rw [le_iff_lt_or_eq] at h
  cases h
  . right; right; assumption
  . right; left; subst x; auto

end TotalOrder

namespace Ordering

def flip : Ordering → Ordering
| lt => gt
| eq => eq
| gt => lt

instance : DecidableEq Ordering
  | x, y => by
cases x <;> cases y <;>
first
 | apply isTrue; refl
 | apply isFalse;
   intro h; cases h

inductive Spec {α} [LT α] (x y : α) : Ordering → Prop
| isLT : x < y → Spec x y lt
| isEQ : x = y → Spec x y eq
| isGT : y < x → Spec x y gt

end Ordering

class DecidableTotalOrder extends TotalOrder α, Ord α where
  compare_eq_lt_iff {x y : α} :
    compare x y = Ordering.lt ↔ x < y
  flip_compare {x y : α} :
    (compare x y).flip = compare y x

namespace DecidableTotalOrder
attribute [simp] compare_eq_lt_iff

open Ord Preorder PartialOrder TotalOrder
variable {α} [LE α] [DecidableTotalOrder α]

@[simp]
theorem compare_eq_eq_iff {x y : α} :
  compare x y = Ordering.eq ↔ x = y := by
constructor <;> intros h
next =>
  apply antisymm
  next =>
    match trichonomy x y with
    | Or.inl h => auto
    | Or.inr (Or.inl h) => auto
    | Or.inr (Or.inr h') =>
      rw [← compare_eq_lt_iff] at h'
      have h₂ := congrArg Ordering.flip h'
      simp [flip_compare,h] at h₂
  next =>
    rw [← not_lt, ← compare_eq_lt_iff, h]
    intro h; cases h
next =>
  subst h
  have h := lt_irrefl x
  rw [← compare_eq_lt_iff] at h
  have h' : ¬ compare x x = Ordering.gt := by
    intros h'; apply h
    have h' := congrArg Ordering.flip h'
    rw [flip_compare] at h'; auto
  cases h : compare x x <;> auto

@[simp]
theorem compare_eq_gt_iff {x y : α} :
  compare x y = Ordering.gt ↔ y < x := by
rw [← compare_eq_lt_iff]
constructor <;> intro h
<;> have h := congrArg Ordering.flip h
<;> simp [flip_compare] at h
<;> assumption

instance : DecidableEq α
| x, y =>
  Decidable.congr compare_eq_eq_iff

instance : @DecidableRel α (.<.)
| x, y => Decidable.congr compare_eq_lt_iff

instance : @DecidableRel α (.≤.)
| x, y => Decidable.congr <| by
  show compare x y ≠ Ordering.gt ↔ x ≤ y
  rw [← not_lt, ← compare_eq_gt_iff]
  refl

instance : BEq α where
  beq x y := decide (x = y)

open Ordering Ordering.Spec

theorem compareSpec (x y : α) : Ordering.Spec x y (compare x y) :=
match h: compare x y with
| lt => isLT (by simp at h; assumption)
| eq => isEQ (by simp at h; assumption)
| gt => isGT (by simp at h; assumption)

theorem compareSpec' {x y : α} {cmp}
  (h : compare x y = cmp):
  Ordering.Spec x y cmp := by
rw [← h]; apply compareSpec

end DecidableTotalOrder

namespace Nat
open Preorder

instance : DecidableTotalOrder Nat where
  antisymm := Nat.le_antisymm
  trans := Nat.le_trans
  lt_iff := by
    intros; rw [Nat.lt_iff_not_le]
    constructor </> auto
    intros h
    constructor </> auto
    have h := Nat.gt_of_not_le h
    auto [Nat.le_of_lt]
  total := Nat.le_total
  compare_eq_lt_iff := by
    intros
    simp [compare, compareOfLessAndEq]
    split; auto
    next x y h =>
      byCases h' : x = y
      next =>
        rw [ite_pos] </> assumption
        constructor
        . intros h; cases h
        . auto
      next =>
        rw [ite_neg] </> assumption
        constructor
        . intros h; cases h
        . auto
  flip_compare := by
    intros; simp [compare, compareOfLessAndEq]
    split
    next x y h =>
      have : ¬ y < x := by
        intros h'; have := Nat.lt_trans h h'
        cases Nat.lt_irrefl _ this
      have : ¬ y = x := by
        intro h; subst h; auto
      simp [*]
    split
    next x y h h' =>
      subst h'
      have h₀ : ¬ x < x := by
        assumption
      simp [h₀]
    next x y h h' =>
      have : y < x := by
        have := Nat.le_of_not_gt h
        rw [Nat.lt_iff_not_le]
        auto [Nat.le_antisymm]
      simp [*]

end Nat
