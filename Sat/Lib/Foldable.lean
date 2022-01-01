
import Sat.Lib.Array.Basic
import Sat.Lib.List.Basic
import Sat.Lib.Monoid

class Foldable (F : Type u → Type v) where
  foldl {α β : Type u} (f : β → α → β) (x₀ : β) (t : F α) : β
  toList {α} (x : F α) : List α := foldl (flip (.::.)) [] x |>.reverse
  toArray {α} (x : F α) : Array α := toList x |>.toArray
  length {α} (x : F α) : Nat :=
    ULift.down <| foldl (λ n _ => ⟨n.1.succ⟩) ⟨0⟩ x

namespace Foldable

variable {F} [Foldable F]
variable {α : Type u}

def foldMap [One m] [Mul m] (f : α → m) (x : F α) : m :=
foldl (λ acc x => f x * acc) One.one x

end Foldable

open One

open Foldable

macro "prove_length_toList" sim:ident α:ident x:ident : tactic =>
  `(tactic|
       -- intros α x;
       suffices H : ((foldl (flip (.::.)) [] x).length =
                 ULift.down (foldl (β := ULift Nat)
                            (λ ⟨n⟩ _ => ⟨n.succ⟩) ⟨0⟩ x))
                by {trans <;> try assumption};
       let R :=
         λ (x : List α) (y : ULift Nat) => x.length = y.down;
       apply sim (SIM := R)
       . apply Reflexive.refl
       . simp [flip]; auto)

macro "prove_foldl_toList" sim:term : tactic =>
  `(tactic|
       intros α β f x₀ x;
       suffices H : ((foldl (flip (.::.)) [] x).foldl f x₀ x =
                 foldl f x₀ x)
                by {trans <;> try assumption};
       let R :=
         λ (x : List α) (y : β) => x.reverse.foldl f x₀ x = y;
       apply sim (SIM := R)
       . apply Reflexive.refl
       . simp [flip]; auto)

class LawfulFoldable (F : Type u → Type v) [Foldable F] where
  foldl_sim {α β γ : Type u} {f : β → α → β} {g : γ → α → γ} {SIM : β → γ → Prop} {x₀ y₀} (t : F α) :
    SIM x₀ y₀ →
    (∀ a x y, SIM x y → SIM (f x a) (g y a)) →
    SIM (foldl f x₀ t) (foldl g y₀ t)
  toArray_toList {α} (x : F α) : (toList x).toArray = toArray x
    -- by apply Reflexive.refl
  length_toList {α} (x : F α) : (toList x).length = length x
 -- :=
 --    -- let H := @foldl_sim
 --    -- by prove_length_toList H α x
 --       have H' : ∀ xs n, List.length xs = n → List.length xs.reverse = n := sorry
 --       suffices H : ((foldl (flip (.::.)) [] x).length =
 --                 ULift.down (foldl (β := ULift Nat)
 --                            (λ ⟨n⟩ _ => ⟨n.succ⟩) ⟨0⟩ x))
 --                by apply H' _ _ H
 --       let R :=
 --         λ (x : List α) (y : ULift Nat) => x.length = y.down;
 --       by apply foldl_sim (SIM := R)
 --          . apply Reflexive.refl
 --          . simp [flip]; auto
  foldl_toList {α β} (f : β → α → β) (x₀ : β) (x : F α) :
    (toList x).foldl f x₀ = foldl f x₀ x
 -- :=
 --    -- let H := @foldl_sim
 --    -- by prove_foldl_toList H
 --       suffices H : ((foldl (flip (.::.)) [] x).reverse.foldl f x₀ =
 --                 foldl f x₀ x)
 --                by {trans <;> try assumption}
 --       let R :=
 --         λ (l : List α) (y : β) => l.reverse.foldl f x₀ = y;
 --       by
 --          apply foldl_sim (SIM := R) x
 --       -- apply sim (SIM := R)
 --          . apply Reflexive.refl
 --          focus simp [flip]

namespace LawfulFoldable
attribute [simp] length_toList toArray_toList

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

theorem foldMap_hom (g₀ : γ → α) (x : F γ) :
  f (foldMap g₀ x) = foldMap (f ∘ g₀) x := by
apply foldl_hom <;> intros <;> simp

@[simp]
theorem toList_toArray {α} (x : F α) : (toArray x).toList = toList x := by
rw [← toArray_toList, Array.toList_toArray]

@[simp]
theorem size_toArray {α} (x : F α) : (toArray x).size = length x := by
rw [← toArray_toList]; simp [-toArray_toList]

theorem foldl_toArray {α β} (f : β → α → β) (x₀ : β) (x : F α) :
    (toArray x).foldl f x₀ = foldl f x₀ x := by
rw [← toArray_toList]; simp [-toArray_toList]
rw [Array.foldl_toArray, foldl_toList]
rw [length_toList]

theorem toList_eq (x : F α) :
  toList x = (foldl (flip (.::.)) [] x).reverse := by
rw [← foldl_toList, List.foldl_eq_self]

theorem toArray_eq (x : F α) :
  toArray x = (foldl Array.push #[] x) := by
rw [← toArray_toList, ← foldl_toList]
generalize toList x = xs; clear x
simp only [List.toArray]
simp [List.toArrayAux, Array.mkEmpty_eq_mkEmpty 0]
generalize (Array.mkEmpty 0) = ar
induction xs generalizing ar
 <;> simp [List.toArrayAux, List.foldl, *]

theorem length_eq (x : F α) :
  length x = ULift.down (foldl (λ ⟨n⟩ _ => ⟨n.succ⟩) ⟨0⟩ x) := by
rw [← length_toList, toList_eq, List.length_reverse]
let R (x : List α) (y : ULift Nat) := x.length = y.down
apply foldl_sim (SIM := R)
. apply Reflexive.refl
intros a xs n; cases n with
  | up n =>
simp [flip]; auto

end LawfulFoldable

instance : Foldable List where
  foldl := List.foldl
  toList := id
  length := List.length

instance : Foldable Array where
  foldl := Array.foldl
  toArray := id
  toList := Array.toList
  length := Array.size

namespace Array


end Array

instance : LawfulFoldable Array where
  foldl_sim :=  by
    intros; apply Array.foldl_sim <;> auto
  toArray_toList :=
    by intros; simp [Array.toArray_toList, toList, toArray]
  length_toList :=
    by intros; simp [toList]; refl
  foldl_toList := by
    intros; simp [toList, foldl]

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
  toArray_toList := by
    intros; simp [toList, toArray]
  length_toList := by
    intros; simp [toList]; refl
  foldl_toList := by
    intros; simp [toList]; refl
