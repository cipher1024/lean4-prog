
import Sat.Lib.Array
import Sat.Lib.Monoid

class Foldable (F : Type u → Type v) where
  foldl {α β : Type u} (f : β → α → β) (x₀ : β) (t : F α) : β

namespace Foldable

variable {F} [Foldable F]
variable {α : Type u}

def foldMap [One m] [Mul m] (f : α → m) (x : F α) : m :=
foldl (λ acc x => f x * acc) One.one x

end Foldable

open One

open Foldable
class LawfulFoldable (F : Type u → Type v) [Foldable F] where
  foldl_sim {α β γ : Type u} {f : β → α → β} {g : γ → α → γ} {SIM : β → γ → Prop} {x₀ y₀} (t : F α) :
    SIM x₀ y₀ →
    (∀ a x y, SIM x y → SIM (f x a) (g y a)) →
    SIM (foldl f x₀ t) (foldl g y₀ t)

namespace LawfulFoldable

variable {F} [Foldable F] [LawfulFoldable F]

theorem foldl_hom {α β γ : Type u} {f : β → α → β} {g : γ → α → γ} {h : β → γ} {x₀ y₀} (t : F α) :
    h x₀ = y₀ →
    (∀ x y, h (f x y) = g (h x) y) →
    h (foldl f x₀ t) = foldl g y₀ t := by
let R x y := h x = y
intros h₀ h₁
apply foldl_sim (SIM := R)
. assumption
. simp only; intros; substAll; apply h₁

variable [Monoid α] [Monoid β]
variable (f : MonoidHom α β)

variable {γ : Type u}

def foldMap_hom (g₀ : γ → α) (x : F γ) :
  f (foldMap g₀ x) = foldMap (f ∘ g₀) x := by
apply foldl_hom <;> intros <;> simp

end LawfulFoldable

instance : Foldable List where
  foldl := List.foldl

instance : Foldable Array where
  foldl := Array.foldl

namespace Array


end Array

instance : LawfulFoldable Array where
  foldl_sim :=  by
    intros; apply Array.foldl_sim <;> auto

namespace List

variable {α β γ : Type u} {f : β → α → β} {g : γ → α → γ} {SIM : β → γ → Prop}
variable  {x₀ y₀} (t : List α)

theorem foldl_sim :
    SIM x₀ y₀ →
    (∀ a x y, SIM x y → SIM (f x a) (g y a)) →
    SIM (foldl f x₀ t) (foldl g y₀ t) := by
induction t generalizing x₀ y₀ <;> auto

end List

instance : LawfulFoldable List where
  foldl_sim :=  by
    intros; apply List.foldl_sim <;> auto
