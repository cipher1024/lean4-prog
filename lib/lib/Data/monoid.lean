
class Zero (α : Type u) where
  zero : α

class One (α : Type u) where
  one : α

open One

class Monoid (α) extends One α, Mul α where
  one_mul {x : α} : one * x = x
  mul_one {x : α} : x * one = x
  mul_assoc {x y z : α} : (x * y) * z = x * (y * z)

attribute [simp] Monoid.one_mul Monoid.mul_one Monoid.mul_assoc

def Additive (α : Type u) := α

class abbrev AddMonoid (α) := Monoid (Additive α)

instance [AddMonoid α] : Add α where
  add := Mul.mul (α := Additive α)

instance [AddMonoid α] : Zero α where
  zero := One.one (α := Additive α)

namespace AddMonoid
open Monoid Zero

variable {α} [AddMonoid α]

@[simp]
theorem add_zero (x : α) : x + zero = x :=
mul_one (α := Additive α)

@[simp]
theorem zero_add (x : α) : zero + x = x :=
one_mul (α := Additive α)

@[simp]
theorem add_assoc (x y z : α) : (x + y) + z = x + (y + z) :=
mul_assoc (α := Additive α)

end AddMonoid


structure MonoidHom (α β) [Monoid α] [Monoid β] where
  fn : α → β
  fn_id : fn one = one
  fn_mul {x y : α} : fn (x * y) = fn x * fn y

instance [Monoid α] [Monoid β] : CoeFun (MonoidHom α β) (λ _ => α → β) where
  coe f := f.fn

attribute [simp] MonoidHom.fn_id MonoidHom.fn_mul

instance : Monoid Nat where
  one := 1
  mul := _
  mul_one := @Nat.mul_one
  one_mul := @Nat.one_mul
  mul_assoc := @Nat.mul_assoc

instance : AddMonoid Nat where
  one := (0 : Nat)
  mul := Nat.add
  mul_one := @Nat.add_zero
  one_mul := @Nat.zero_add
  mul_assoc := @Nat.add_assoc

def Endo (α : Sort u) := α → α
def Endo.mk (f : α → α) : Endo α := f
def Endo.run (f : Endo α) : α → α := f

instance : Monoid (Endo α) where
  one := id
  mul := (.∘.)
  mul_one := rfl
  one_mul := rfl
  mul_assoc := rfl

namespace End

@[simp]
theorem run_one :
  @Endo.run α One.one x = x := rfl

@[simp]
theorem run_mk {α} x a :
  @Endo.run α (Endo.mk x) a = x a := rfl

@[simp]
theorem run_mul_mk {α} (x : α → α) y a :
  @Endo.run α (Endo.mk x * y) a = x (Endo.run y a) := rfl

@[simp]
theorem run_mul_mk' {α} x y a :
  @Endo.run α (x * Endo.mk y) a = Endo.run x (y a) := rfl

end End

def Op (α : Sort u) := α
def Op.mk (f : α) : Op α := f
def Op.run (f : Op α) : α := f

instance [Monoid α] : Monoid (Op α) where
  one := one (α := α)
  mul (x y : α) := y * x
  mul_one := @Monoid.one_mul α _
  one_mul := @Monoid.mul_one α _
  mul_assoc {x y z} := @Monoid.mul_assoc α _ z y x |>.symm

namespace Op

@[simp]
theorem Op.run_mk [Monoid α] (x : α) :
  Op.run (Op.mk x) = x := rfl

@[simp]
theorem Op.run_one [Monoid α] :
  Op.run One.one = One.one (α := α) := rfl

@[simp]
theorem Op.run_mul [Monoid α] (x y : Op α) :
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
