
import Lib.Algebra.Monoid
import Lib.Data.Array.Basic
import Lib.Function

class Foldable (F : Type u → Type v) where
  foldl {α β : Type u} (f : β → α → β) (x₀ : β) (t : F α) : β
  foldr {α β : Type u} (f : α → β → β) (x₀ : β) (t : F α) : β
  toList {α} (x : F α) : List α := foldl (flip (.::.)) [] x |>.reverse
  toArray {α} (x : F α) : Array α := toList x |>.toArray
  length {α} (x : F α) : Nat :=
    ULift.down <| foldl (λ n _ => ⟨n.1.succ⟩) ⟨0⟩ x

namespace Foldable

variable {F} [Foldable F]
variable {α : Type u}

def foldMap [One m] [Mul m] (f : α → m) (x : F α) : m :=
foldl (λ acc x => f x * acc) One.one x

def sum [Zero α] [Add α] : F α → α :=
foldl (.+.) Zero.zero

def product [One α] [Mul α] : F α → α :=
foldl (.*.) One.one

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
  foldr_eq_foldMap {α β} (f : α → β → β) (x : F α) (x₀ : β) :
    foldr f x₀ x =
    (foldMap (λ x => Op.mk $ Endo.mk (f x)) x).run.run x₀
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

theorem foldl_eq_foldMap (f : β → α → β) (x₀ : β) (x : F α) :
  foldl f x₀ x = (foldMap (λ a => Endo.mk (f . a)) x).run x₀ := by
  intros; simp [foldMap]
  let g := (fun acc x => Endo.mk (λ a => f a x) * acc)
  symmetry
  apply foldl_hom (h := λ x => Endo.run x x₀) (f := g) (g := f)
  . refl
  intros; simp

theorem foldr_toList
  (f : α → β → β) (x₀ : β) (x : F α) :
  List.foldr f x₀ (toList x) = foldr f x₀ x := by
rw [← flip_flip f, ← List.foldl_reverse, foldr_eq_foldMap]
simp only [foldMap]
rw [← foldl_toList]
symmetry
generalize toList x = l
rw [flip_flip]
have : ∀ x y : β, x = Endo.run (Op.run one) y → x = y :=
  by auto
apply this; clear this
generalize one (α := Op (Endo β)) = k
induction l generalizing k
 <;> simp [List.foldl, *]

theorem foldr_eq_foldl_reverse_toList
  (f : α → β → β) (x₀ : β) (x : F α) :
  foldr f x₀ x = List.foldl (flip f) x₀ (toList x).reverse := by
simp [← foldr_toList]

theorem foldr_sim {SIM : β → γ → Prop}
        {f : α → β → β} {g : α → γ → γ}
        {x₀ : β} {y₀ : γ} {x : F α}
        (H₀ : SIM x₀ y₀)
        (Hstep : ∀ x y y', SIM y y' → SIM (f x y) (g x y')) :
  SIM (foldr f x₀ x) (foldr g y₀ x) := by
repeat rw [foldr_eq_foldl_reverse_toList]
auto [List.foldl_sim]

theorem foldr_hom {f : α → β → β} {g : α → γ → γ}
        {h : β → γ} {x₀ y₀} (t : F α) :
    h x₀ = y₀ →
    (∀ x y, h (f x y) = g x (h y)) →
    h (foldr f x₀ t) = foldr g y₀ t := by
let R x y := h x = y
intros h₀ h₁
apply foldr_sim (SIM := R)
. assumption
. simp only; intros; substAll; apply h₁
done

end LawfulFoldable
