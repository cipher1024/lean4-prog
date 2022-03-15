
import Lib.Algebra.Group

class LeftDistrib (α : Type u) [Mul α] [Add α] where
  left_distrib {x y z : α} : x * (y + z) = x * y + x * z

class RightDistrib (α : Type u) [Mul α] [Add α] where
  right_distrib {x y z : α} : (x + y) * z = x*z + y*z

class SemiRing (α : Type u) where
-- extends AddCommMonoid α, Monoid α where
  [mul_monoid : Monoid α]
  [add_monoid : AddCommMonoid α]
  [left_distr : LeftDistrib α]
  [right_distr : RightDistrib α]
  mul_zero {x : α} : x * 0 = 0
  zero_mul {x : α} : 0 * x = 0

namespace SemiRing
attribute [instance] mul_monoid add_monoid left_distr right_distr

variable [SemiRing α]

end SemiRing

class Ring (α : Type u) where
  [mul_monoid : Monoid α]
  [add_group : CommAddGroup α]
  [left_distr : LeftDistrib α]
  [right_distr : RightDistrib α]
  mul_zero {x : α} : x * 0 = 0
  zero_mul {x : α} : 0 * x = 0

attribute [instance] Ring.mul_monoid Ring.add_group
attribute [instance] Ring.left_distr Ring.right_distr

namespace Ring
variable [Ring α]
variable {x y z : α}
open LeftDistrib RightDistrib AddGroup Ring

theorem neg_mul : -x * y = -(x * y) := by
symmetry
rw [neg_eq_iff_l, ← right_distrib, add_neg, zero_mul]

theorem mul_neg : x * -y = -(x * y) := by
symmetry
rw [neg_eq_iff_l, ← left_distrib, add_neg, mul_zero]

theorem neg_mul_eq_mul_neg : -x * y = x * -y := by
rw [neg_mul, mul_neg]

end Ring

class OrderedRing (α : Type u) [LE α] where
  [mul_monoid : OrderedMonoid α]
  [add_group : OrderedCommAddGroup α]
  [left_distr : LeftDistrib α]
  [right_distr : RightDistrib α]
  mul_zero {x : α} : x * 0 = 0
  zero_mul {x : α} : 0 * x = 0

attribute [instance] OrderedRing.mul_monoid OrderedRing.add_group
attribute [instance] OrderedRing.left_distr OrderedRing.right_distr

instance [LE α] [OrderedRing α] : OfNat α (nat_lit 1) := inferInstance
instance [LE α] [OrderedRing α] : OfNat α (nat_lit 0) := inferInstance
-- instance [LE α] [Ring α] : Monoid α := inferInstance
-- instance [LE α] [Ring α] : AddGroup α := inferInstance

namespace OrderedRing
variable [LE α] [OrderedRing α]

instance : Ring α where
  mul_monoid := inferInstance
  add_group  := inferInstance
  left_distr := inferInstance
  right_distr := inferInstance
  mul_zero := OrderedRing.mul_zero
  zero_mul := OrderedRing.zero_mul

instance : CommAddGroup α :=
OrderedRing.add_group.toCommGroup (α := Additive α)

instance : AddCommMonoid α := inferInstance
-- OrderedRing.add_group.toCommGroup (α := Additive α)

end OrderedRing

namespace Nat

instance : LeftDistrib Nat where
  left_distrib := @Nat.left_distrib

instance : RightDistrib Nat where
  right_distrib := @Nat.right_distrib

instance : SemiRing Nat where
  mul_monoid := inferInstanceAs (Monoid Nat)
  add_monoid := inferInstanceAs (AddCommMonoid Nat)
  left_distr := inferInstance
  right_distr := inferInstance
  mul_zero := @Nat.mul_zero
  zero_mul := @Nat.zero_mul

end Nat
