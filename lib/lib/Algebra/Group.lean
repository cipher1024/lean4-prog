
import Lib.Algebra.Monoid
import Lib.Logic.Basic
import Lib.Order.Basic
import Lib.Tactic
import Lib.Util

class Group (α : Type u) extends Monoid α where
  inv : α → α
  mul_inv (x : α) : x * inv x = 1

namespace Group
open Monoid

variable [Group α]

attribute [simp] mul_inv

notation x "⁻¹" => inv x

theorem inv_unique {a x y : α}
        (hx : x * a = 1)
        (hy : a * y = 1) :
  x = y :=
calc
  x = x *  1      := by rw [mul_one]
  _ = x * (a * y) := by rw [hy]
  _ = (x * a) * y := by rw [mul_assoc]
  _ = y           := by rw [hx, one_mul]

theorem inv_unique' {a x : α}
        (hx : x * a = 1) :
  x = a⁻¹ :=
inv_unique hx <| mul_inv _

@[simp]
theorem inv_inv (a : α) : a⁻¹⁻¹ = a :=
inv_unique' (mul_inv _) |>.symm

@[simp]
theorem inv_mul (x : α) : x⁻¹ * x = 1 := by
have := mul_inv (inv x)
rw [inv_inv] at this; assumption

@[simp]
theorem inv_one : 1⁻¹ = (1 : α) :=
calc
  1⁻¹ =@{α} 1 * 1⁻¹ := by rw [one_mul]
  _   =@{α} 1       := by rw [mul_inv]

theorem inv_injective {x y : α} :
  x⁻¹ = y⁻¹ ↔ x = y := by
constructor <;> intro h
next =>
  rw [← inv_inv x, h, inv_inv]
next =>
  apply congrArg _ h

theorem inv_eq_iff_l {x y : α} :
  x⁻¹ = y ↔ 1 = x * y := by
constructor <;> intro h
next =>
  exact calc
    1 =@{α} x * x⁻¹ := by simp
    _     = x * y := by rw [h]
next =>
  exact calc
    x⁻¹ = x⁻¹ * 1 := by simp
    _   = x⁻¹ * x * y := by rw [h, mul_assoc]
    _   = 1 * y := by simp
    _   = y := by simp

theorem inv_eq_iff_r {x y : α} :
  x⁻¹ = y ↔ 1 = y * x := by
rw [← inv_inv y, ← inv_eq_iff_l, inv_injective, inv_inv]
apply Eq.comm

theorem mul_cancel_iff_l {x y z : α} :
  x⁻¹ * z = y ↔ z = x * y := by
constructor <;> intro h
next =>
  exact calc
    z =@{α} x * x⁻¹ * z := by simp
    _     = x * y       := by rw [← h, mul_assoc]
next =>
  exact calc
    x⁻¹ * z = x⁻¹ * x * y := by rw [h, mul_assoc]
    _       = 1 * y := by simp
    _       = y := by simp

@[simp]
theorem inv_mul_inv {x y : α } :
  (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
rw [inv_eq_iff_r]; symmetry
exact calc
  (y⁻¹ * x⁻¹) * (x * y) = y⁻¹ * (x⁻¹ * x) * y :=
    by simp only [mul_assoc]
  _                     = y⁻¹ * 1 * y         :=
    by rw [inv_mul]
  _                     =@{α} 1               :=
    by rw [mul_one, inv_mul]

theorem mul_cancel_iff_r {x y z : α} :
  z * x⁻¹ = y ↔ z = y * x := by
rw [← inv_injective, inv_mul_inv, mul_cancel_iff_l]
rw [← inv_mul_inv, inv_injective]
refl

end Group

abbrev AddGroup (α : Type u) := Group (Additive α)

namespace AddGroup
open Group

variable [AddGroup α]

def neg (x : α) : α := inv (α := Additive α) x

instance : Neg α := ⟨ neg ⟩

instance : Sub α where
  sub x y := x + -y

@[simp]
theorem neg_zero : (- 0 : α) = 0 :=
Group.inv_one (α := Additive α)

@[simp]
theorem neg_neg (x : α) : - - x = x :=
Group.inv_inv (α := Additive α) _

@[simp]
theorem neg_add (x : α) : - x + x = 0 :=
Group.inv_mul (α := Additive α) _

@[simp]
theorem add_neg (x : α) : x + - x = 0 :=
Group.mul_inv (α := Additive α) _

theorem neg_eq_iff_l {x y : α} :
  -x = y ↔ 0 = x + y :=
Group.inv_eq_iff_l (α := Additive α)

theorem neg_eq_iff_r {x y : α} :
  -x = y ↔ 0 = y + x :=
Group.inv_eq_iff_r (α := Additive α)

@[simp]
theorem neg_add_neg (x y : α) : -(x + y) = -y + -x :=
Group.inv_mul_inv (α := Additive α)

theorem add_cancel_iff_l {x y z : α} :
  -x + z = y ↔ z = x + y :=
Group.mul_cancel_iff_l (α := Additive α)

theorem add_cancel_iff_r {x y z : α} :
  z + -x = y ↔ z = y + x :=
Group.mul_cancel_iff_r (α := Additive α)

end AddGroup

class OrderedGroup (α : Type u) [LE α]
extends Group α where
  mul_le_mul {x x' y y' : α} :
    x ≤ x' →
    y ≤ y' →
    x * y ≤ x' * y'

namespace OrderedGroup
open Monoid Group OrderedMonoid

variable [LE α] [OG : OrderedGroup α]

instance : OrderedMonoid α :=
{ OG.toMonoid with
  mul_le_mul := OrderedGroup.mul_le_mul }

variable [Preorder α]

open Reflexive

@[auto]
theorem inv_le_inv {x y : α} :
  x ≤ y → y⁻¹ ≤ x⁻¹ := by
intros h
suffices (x⁻¹ * x) * y⁻¹ ≤ x⁻¹ * 1
  by simp [- mul_assoc] at this; auto
rw [mul_assoc]
apply mul_le_mul_r (α := α)
suffices x * y⁻¹ ≤ y * y⁻¹
  by simp at this; auto
auto [mul_le_mul_l]

theorem inv_le_inv_iff {x y : α} :
  x⁻¹ ≤ y⁻¹ ↔ y ≤ x := by
constructor <;> intros h
next =>
  have h := inv_le_inv h
  simp at h; assumption
next =>
  auto

theorem inv_le_one {x : α} :
  x⁻¹ ≤ 1 ↔ 1 ≤ x :=
by rw [← inv_le_inv_iff]; simp

theorem one_le_inv {x : α} :
  1 ≤ x⁻¹ ↔ x ≤ 1 :=
by rw [← inv_le_inv_iff]; simp

theorem inv_mul_le_cancel_l {x y z : α} :
  x⁻¹ * y ≤ z ↔ y ≤ x * z := by
constructor <;> intros h
next =>
  trans 1 * y
  next => rw [one_mul]; refl
  next =>
    rw [← mul_inv (x := x), mul_assoc]
    auto [mul_le_mul_r]
next =>
  rw [← one_mul (x := z), ← inv_mul (x := x), mul_assoc]
  auto [mul_le_mul_r]

theorem inv_mul_le_cancel_r {x y z : α} :
  x * y⁻¹ ≤ z ↔ x ≤ z * y := by
rw [← inv_le_inv_iff, inv_mul_inv, ← inv_mul_le_cancel_l]
rw [← inv_mul_inv, inv_le_inv_iff, inv_inv]
refl

end OrderedGroup

instance [LE α] [I : Preorder α] : Preorder (Additive α) := I

abbrev AddOrderedGroup (α : Type u) [LE α] :=
OrderedGroup (Additive α)

namespace AddOrderedGroup
open OrderedGroup Reflexive

section abs
variable [LT α] [Neg α] [@DecidableRel α LT.lt]

def abs (x : α) : α :=
max x (-x)

end abs

section Preorder
variable [LE α] [Preorder α]

variable [AddOrderedGroup α]
open AddMonoid AddGroup AddOrderedMonoid

@[auto]
theorem neg_le_neg {x y : α} :
  x ≤ y → - y ≤ - x := by
intros h
suffices (-x + x) + -y ≤ - x + 0
  by simp at this; auto
rw [add_assoc]
apply add_le_add_r (α := α)
suffices x + -y ≤ y + -y
  by simp at this; auto
apply add_le_add_l (α := α) h

@[simp]
theorem neg_le_neg_iff {x y : α} :
  - x ≤ - y ↔ y ≤ x := by
constructor <;> intros h
next =>
  have h := neg_le_neg h
  simp at h; assumption
next =>
  auto

@[simp]
theorem neg_le_zero {x : α} :
  - x ≤ 0 ↔ 0 ≤ x :=
by rw [← neg_le_neg_iff]; simp

@[simp]
theorem zero_le_neg {x : α} :
  0 ≤ -x ↔ x ≤ 0 :=
by rw [← neg_le_neg_iff]; simp

theorem neg_add_le_cancel_l {x y z : α} :
  -x + y ≤ z ↔ y ≤ x + z :=
inv_mul_le_cancel_l (α := Additive α)

theorem neg_add_le_cancel_r {x y z : α} :
  x + -y ≤ z ↔ x ≤ z + y :=
inv_mul_le_cancel_r (α := Additive α)

end Preorder

open TotalOrder
variable [LE α] [DecidableTotalOrder α]
variable [AddOrderedGroup α]

@[auto]
theorem abs_nonneg {x : α} : 0 ≤ abs x := by
simp [abs, zero_le_neg, total]

@[simp]
theorem abs_le_iff {x z : α} : abs x ≤ z ↔ x ≤ z ∧ -x ≤ z := by
simp [abs]

@[simp]
theorem le_abs_iff {x z : α} :
  z ≤ abs x ↔ z ≤ x ∨ z ≤ -x := by
simp [abs]

@[auto]
theorem le_abs_self {x : α} :
  x ≤ abs x :=
by simp; left; refl

@[auto]
theorem neg_le_abs_self {x : α} :
  -x ≤ abs x :=
by simp; right; refl

end AddOrderedGroup

class CommGroup (α : Type u) extends Group α where
  mul_comm {x y : α} : x * y = y * x

instance [G : CommGroup α] : CommMonoid α :=
{ G.toGroup.toMonoid with
  mul_comm := CommGroup.mul_comm }

abbrev CommAddGroup (α : Type u) :=
CommGroup (Additive α)

namespace CommAddGroup

variable [CommAddGroup α]

theorem add_comm {x y : α} : x + y = y + x :=
CommGroup.mul_comm (α := Additive α)

end CommAddGroup

class abbrev OrderedCommGroup (α : Type u) [LE α] :=
 CommGroup α, OrderedGroup α

abbrev OrderedCommAddGroup (α : Type u) [LE α] :=
OrderedCommGroup (Additive α)

instance [LE α] [OrderedCommAddGroup α] : AddOrderedGroup α :=
inferInstance

namespace OrderedCommAddGroup
variable [LE α] [DecidableTotalOrder α] [OrderedCommAddGroup α]

open AddOrderedMonoid AddGroup AddMonoid
open DecidableTotalOrder AddOrderedGroup CommAddGroup

theorem triangle_ineq {x y : α} :
  abs (x + y) ≤ abs x + abs y := by
rw [abs_le_iff (α := α)]
constructor
next =>
  apply add_le_add (α := α) <;> auto
next =>
  rw [add_comm, neg_add_neg]
  apply add_le_add (α := α) <;> auto

end OrderedCommAddGroup
