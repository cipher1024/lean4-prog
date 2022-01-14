
import Lib.Algebra.Monoid
import Lib.Data.MonoFoldable
import Lib.Data.MonoFunctor
import Lib.Data.Traversable
import Lib.Function

class MonoTraversable (T : Type u) (α : outParam (Type u))
extends MonoFunctor T α, MonoFoldable T α where
  traverse {F : Type u → Type u} [Applicative F] (f : α → F α) : T → F T
  mapM {F : Type u → Type u} [Monad F] (f : α → F α) : T → F T

instance {T} [Traversable T] : MonoTraversable (T α) α where
  traverse := Traversable.traverse
  mapM := Traversable.mapM

namespace MonoTraversable

open MonoTraversable
-- open Traversable (StateT.mk)
-- def StateT.mk {σ α} (f : σ → m (α × σ)) : StateT σ m α := f

section Accum

variable {T : Type u} [MonoTraversable T α]
variable (f : α → σ → α × σ)

def accuml (x₀ : σ) (x : T) : T × σ :=
StateT.run (m := Id) (mapM (StateT.mk.{u,u} ∘ f) x) x₀

def scanl (x₀ : σ) (x : T) : T :=
StateT.run' (m := Id) (mapM (StateT.mk.{u,u} ∘ f) x) x₀

def accumr (x₀ : σ) (x : T) : T × σ :=
StateT.run (m := Id) (Op1.run (traverse (Op1.mk.{u,u} ∘ StateT.mk.{u,u} ∘ f) x)) x₀

def scanr (x₀ : σ) (x : T) : T :=
accumr f x₀ x |>.1

end Accum

section AccumIdx

variable {T : Type u} [MonoTraversable.{u} T α]
variable {β : Type u} (f : Nat → α → σ → α × σ)

def accumlIdx (x₀ : σ) (x : T) : T × σ :=
accuml (λ a (x, i) => f i a x |>.map id (., i+1)) (x₀, 0) x |>.map id Prod.fst

def scanlIdx (x₀ : σ) (x : T) : T :=
accumlIdx f x₀ x |>.fst

end AccumIdx
end MonoTraversable

open MonoTraversable
class LawfulMonoTraversable (T : Type u) (α : Type u)
      [MonoTraversable T α]
extends LawfulMonoFunctor T α, LawfulMonoFoldable T α where
  traverse_eq_mapM {M} [Monad M] [LawfulMonad M] (f : α → M α) (x : T) :
    traverse f x = mapM f x
  map_eq_traverse (f : α → α) (x : T) :
    MonoFunctor.map f x = Id.run (traverse (Id.mk ∘ f) x)
  -- id_traverse {α} (x : T α) : traverse Id.mk x = Id.mk x
  comp_traverse {F G} [Applicative F] [LawfulApplicative F]
    [Applicative G] [LawfulApplicative G]
    (x : T) (f : α → F α) (g : α → G α) :
    Comp.run (traverse (Comp.mk ∘ Functor.map f ∘ g) x) =
    traverse f <$> traverse g x
  foldl_eq_traverse {β} (f : β → α → β) (x : T) (x₀ : β) :
    MonoFoldable.foldl f x₀ x =
    Endo.run (Op.run (Const.run (traverse
      (Const.mk (α := α) ∘ Op.mk ∘ Endo.mk ∘ flip f) x))) x₀
  traverse_sim {F G}
               [Applicative F] [LawfulApplicative F]
               [Applicative G] [LawfulApplicative G]
               (x : T) (R : ApplicativeRel F G)
               (f : α → F α) (g : α → G α) :
      (∀ a, R (f a) (g a)) →
      R (traverse f x) (traverse g x)

instance {T} [Traversable T] [LawfulTraversable T] :
         LawfulMonoTraversable (T α) α where
  traverse_eq_mapM := LawfulTraversable.traverse_eq_mapM
  map_eq_traverse := LawfulTraversable.map_eq_traverse
  comp_traverse := LawfulTraversable.comp_traverse
  foldl_eq_traverse := LawfulTraversable.foldl_eq_traverse
  traverse_sim := LawfulTraversable.traverse_sim

namespace LawfulMonoTraversable
open MonoTraversable

variable {T} [MonoTraversable T α] [LawfulMonoTraversable T α]

theorem id_traverse (x : T) : traverse Id.mk x = Id.mk x := by
have := (map_eq_traverse id x).symm
simp [LawfulMonoFunctor.id_map] at this
assumption

section nat
variable {T : Type u} [MonoTraversable T α] [LawfulMonoTraversable T α]
variable {F : Type u → Type u} [Applicative F] [LawfulApplicative F]
variable {G : Type u → Type u} [Applicative G] [LawfulApplicative G]

theorem traverse_nat (x : T) (f : ApplicativeHom F G)
        (g : α → F α) :
  f (traverse g x) = traverse (f.fn ∘ g) x := by
let R := f.toApplicativeRel
apply LawfulMonoTraversable.traverse_sim _ R; intro a
simp [ApplicativeHom.toApplicativeRel]

end nat

end LawfulMonoTraversable
