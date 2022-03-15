
import Lib.Logic.Relation
import Lib.Order.Basic

-- class abbrev Zero (α : Type u) := OfNat α (nat_lit 0)
-- class abbrev One (α : Type u) := OfNat α (nat_lit 1)

class Zero (α : Type u) where
  zero : α

instance [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

class One (α : Type u) where
  one : α

instance [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

open One

class Monoid (α : Type u) extends One α, Mul α where
  one_mul {x : α} : 1 * x = x
  mul_one {x : α} : x * 1 = x
  mul_assoc {x y z : α} : (x * y) * z = x * (y * z)

attribute [simp] Monoid.one_mul Monoid.mul_one Monoid.mul_assoc

def Additive (α : Type u) := α

abbrev AddMonoid (α) := Monoid (Additive α)

instance [AddMonoid α] : Add α where
  add := Mul.mul (α := Additive α)

instance [AddMonoid α] : Zero α where
  zero := One.one (α := Additive α)

namespace AddMonoid
open Monoid Zero

variable {α} [AddMonoid α]

@[simp]
theorem add_zero (x : α) : x + 0 = x :=
have := mul_one (α := Additive α) (x := x)
this

@[simp]
theorem zero_add (x : α) : 0 + x = x :=
have := one_mul (α := Additive α) (x := x)
this

@[simp]
theorem add_assoc (x y z : α) : (x + y) + z = x + (y + z) :=
mul_assoc (α := Additive α)

end AddMonoid

class CommMonoid (α : Type u)
extends Monoid α where
  mul_comm {x y : α} : x * y = y * x

abbrev AddCommMonoid (α : Type u) :=
CommMonoid (Additive α)

namespace AddCommMonoid
variable [AddCommMonoid α]

theorem add_comm {x y : α} : x + y = y + x :=
CommMonoid.mul_comm (α := Additive α)

end AddCommMonoid

instance [LE α] : LE (Additive α) where
  le := LE.le (α := α)

class OrderedMonoid (α : Type u) [LE α]
extends Monoid α where
  mul_le_mul {x x' y y' : α} :
    x ≤ x' →
    y ≤ y' →
    x * y ≤ x' * y'

namespace OrderedMonoid
open Reflexive
variable [LE α] [Preorder α] [OrderedMonoid α]

theorem mul_le_mul_l {x x' y : α}
        (h : x ≤ x') :
  x * y ≤ x' * y :=
mul_le_mul h <| refl _

theorem mul_le_mul_r {x y y' : α}
        (h : y ≤ y') :
  x * y ≤ x * y' :=
mul_le_mul (refl _) h

end OrderedMonoid

-- @[class]
abbrev AddOrderedMonoid (α : Type u) [LE α] :=
OrderedMonoid (Additive α)


namespace AddOrderedMonoid
open Reflexive
variable [LE α] [AddOrderedMonoid α]

theorem add_le_add {x x' y y' : α} :
    x ≤ x' →
    y ≤ y' →
    x + y ≤ x' + y' :=
OrderedMonoid.mul_le_mul (α := Additive α)

variable [Preorder α]

theorem add_le_add_l {x x' y : α}
        (h : x ≤ x') :
  x + y ≤ x' + y :=
add_le_add h <| refl _

theorem add_le_add_r {x y y' : α}
        (h : y ≤ y') :
  x + y ≤ x + y' :=
add_le_add (refl _) h

end AddOrderedMonoid

structure MonoidHom (α β) [Monoid α] [Monoid β] where
  fn : α → β
  fn_id : fn 1 = 1
  fn_mul {x y : α} : fn (x * y) = fn x * fn y

instance [Monoid α] [Monoid β] : CoeFun (MonoidHom α β) (λ _ => α → β) where
  coe f := f.fn

attribute [simp] MonoidHom.fn_id MonoidHom.fn_mul

instance : CommMonoid Nat where
  one := 1
  mul := _
  mul_one := @Nat.mul_one
  one_mul := @Nat.one_mul
  mul_assoc := @Nat.mul_assoc
  mul_comm := @Nat.mul_comm

instance : AddCommMonoid Nat where
  one := (0 : Nat)
  mul := Nat.add
  mul_one := @Nat.add_zero
  one_mul := @Nat.zero_add
  mul_assoc := @Nat.add_assoc
  mul_comm := @Nat.add_comm

def Endo (α : Sort u) := α → α
def Endo.mk (f : α → α) : Endo α := f
def Endo.run (f : Endo α) : α → α := f

instance : Monoid (Endo α) where
  one := id
  mul := (.∘.)
  mul_one := rfl
  one_mul := rfl
  mul_assoc := rfl

namespace Endo

@[simp]
theorem run_one :
  @Endo.run α (1 : Endo α) x = x := rfl

@[simp]
theorem run_one' :
  @Endo.run α one x = x := rfl

@[simp]
theorem run_mk {α} x a :
  @Endo.run α (Endo.mk x) a = x a := rfl

@[simp]
theorem run_mul_mk {α} (x : α → α) y a :
  @Endo.run α (Endo.mk x * y) a = x (Endo.run y a) := rfl

@[simp]
theorem run_mul_mk' {α} x y a :
  @Endo.run α (x * Endo.mk y) a = Endo.run x (y a) := rfl

end Endo

def Op (α : Sort u) := α
def Op.mk (f : α) : Op α := f
def Op.run (f : Op α) : α := f

instance [Monoid α] : Monoid (Op α) where
  one := (1 : α)
  mul (x y : α) := y * x
  mul_one := @Monoid.one_mul α _
  one_mul := @Monoid.mul_one α _
  mul_assoc {x y z} := @Monoid.mul_assoc α _ z y x |>.symm

namespace Op

@[simp]
theorem run_mk [Monoid α] (x : α) :
  Op.run (Op.mk x) = x := rfl

@[simp]
theorem run_one' [Monoid α] :
  Op.run one = one (α := α) := rfl

@[simp]
theorem run_one [Monoid α] :
  Op.run (1 : α) = 1 := rfl

@[simp]
theorem run_mul [Monoid α] (x y : Op α) :
  Op.run (x * y) = y.run * x.run := rfl

end Op

namespace Monoid

structure Max (α : Type u) where
  get : Option α
structure Min (α : Type u) where
  get : Option α
structure Sum (α : Type u) where
  get : α

-- instance [LT α] [DecidableRel LT.lt (α := α)] : Monoid (Max α) where
--   one := ⟨ none ⟩
--   mul
--     | ⟨ some x ⟩, ⟨ some y ⟩ => ⟨ some (max x y) ⟩
--     | ⟨ none ⟩, x => x
--     | x, ⟨ none ⟩ => x

end Monoid
