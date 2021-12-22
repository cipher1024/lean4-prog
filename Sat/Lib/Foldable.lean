
import Sat.Lib.Array

-- #check Add
class One (α : Type u) where
  one : α

class Foldable (F : Type u → Type v) where
  foldl {α β : Type u} (f : β → α → β) (x₀ : β) (t : F α) : β

namespace Foldable

variable {F} [Foldable F]
variable {α : Type u}

def foldMap [One m] [Mul m] (f : α → m) (x : F α) : m :=
foldl (λ acc x => f x * acc) One.one x

end Foldable

open One

class Monoid (α) extends One α, Mul α where
  one_mul {x : α} : one * x = x
  mul_one {x : α} : x * one = x
  mul_assoc {x y z : α} : (x * y) * z = x * (y * z)

structure MonoidHom (α β) [Monoid α] [Monoid β] where
  fn : α → β
  fn_id : fn one = one
  fn_mul {x y : α} : fn (x * y) = fn x * fn y

instance [Monoid α] [Monoid β] : CoeFun (MonoidHom α β) (λ _ => α → β) where
  coe f := f.fn

attribute [simp] MonoidHom.fn_id MonoidHom.fn_mul

open Foldable
class LawfulFoldable (F : Type u → Type v) [Foldable F] where
  foldl_hom {α β γ : Type u} {f : β → α → β} {g : γ → α → γ} {h : β → γ} {x₀ y₀} (t : F α) :
    h x₀ = y₀ →
    (∀ x y, h (f x y) = g (h x) y) →
    h (foldl f x₀ t) = foldl g y₀ t

namespace LawfulFoldable

variable [Monoid α] [Monoid β]
variable (f : MonoidHom α β)

variable {F} [Foldable F][LawfulFoldable F]
variable {γ : Type u}

def foldMap_hom (g₀ : γ → α) (x : F γ) :
  f (foldMap g₀ x) = foldMap (f ∘ g₀) x := by
apply foldl_hom <;> intros <;> simp

end LawfulFoldable

instance : Foldable Array where
  foldl := Array.foldl

instance : LawfulFoldable Array where
  foldl_hom t := Array.foldl_hom _ _ _ _ t
