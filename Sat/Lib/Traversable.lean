-- TODO: generate point-free lemmas
-- use registerSimpAttr to create simp rewrite sets

import Sat.Lib.Functor
import Sat.Lib.Monoid
import Sat.Lib.Foldable

class Traversable (T : Type u → Type u) extends Functor T, Foldable T where
  traverse {F : Type u → Type u} [Applicative F] (f : α → F β) : T α → F (T β)
  mapM {F : Type u → Type u} [Monad F] (f : α → F β) : T α → F (T β)

namespace Traversable
end Traversable

instance : Traversable Array where
  map := Array.map
  traverse := Array.mapA
  mapM := Array.mapM

instance : Traversable List where
  map := List.map
  traverse := List.mapA
  mapM := List.mapM

open Traversable

def StateT.mk {σ α} (f : σ → m (α × σ)) : StateT σ m α := f

section Accum

variable {T : Type u → Type u} [Traversable T]
variable {α β : Type u} (f : α → σ → β × σ)

def accuml (x₀ : σ) (x : T α) : T β × σ :=
StateT.run (m := Id) (mapM (StateT.mk.{u,u} ∘ f) x) x₀

def scanl (x₀ : σ) (x : T α) : T β :=
accuml f x₀ x |>.1

def accumr (x₀ : σ) (x : T α) : T β × σ :=
StateT.run (m := Id) (Op1.run (traverse (Op1.mk.{u,u} ∘ StateT.mk.{u,u} ∘ f) x)) x₀

def scanr (x₀ : σ) (x : T α) : T β :=
accumr f x₀ x |>.1

end Accum

class LawfulTraversable (T : Type u → Type u) [Traversable T]
extends LawfulFunctor T, LawfulFoldable T where
  traverse_eq_mapM {α β} {M} [Monad M] [LawfulMonad M] (f : α → M β) (x : T α) :
    traverse f x = mapM f x
  map_eq_traverse {α β} (f : α → β) (x : T α) :
    Functor.map f x = Id.run (traverse (Id.mk ∘ f) x)
  -- id_traverse {α} (x : T α) : traverse Id.mk x = Id.mk x
  comp_traverse {α} {F G} [Applicative F] [LawfulApplicative F]
    [Applicative G] [LawfulApplicative G]
    (x : T α) (f : β → F γ) (g : α → G β) :
    traverse (Comp.mk ∘ Functor.map f ∘ g) x = traverse f <$> traverse g x
  foldl_eq_traverse {α β} (f : β → α → β) (x : T α) (x₀ : β) :
    Foldable.foldl f x₀ x =
    Endo.run (Const.run (traverse (Const.mk (α := α) ∘ Endo.mk ∘ flip f) x)) x₀

  traverse_sim {α} {F G}
               [Applicative F] [LawfulApplicative F]
               [Applicative G] [LawfulApplicative G]
               (x : T α) (R : ApplicativeRel F G)
               (f : α → F β) (g : α → G β) :
      (∀ a, R (f a) (g a)) →
      R (traverse f x) (traverse g x)

  -- traverse_nat {α} {F G} [Applicative F] [LawfulApplicative F]
  --   [Applicative G] [LawfulApplicative G]
  --   (x : T α) (f : ApplicativeHom F G) (g : α → F β) :
  --     f (traverse g x) = traverse (f.fn ∘ g) x

namespace LawfulTraversable

variable {T} [Traversable T] [LawfulTraversable T]

theorem id_traverse {α} (x : T α) : traverse Id.mk x = Id.mk x := by
have := (map_eq_traverse id x).symm
simp [id_map] at this; assumption

section nat
variable {T : Type u → Type u} [Traversable T] [LawfulTraversable T]
variable {F : Type u → Type u} [Applicative F] [LawfulApplicative F]
variable {G : Type u → Type u} [Applicative G] [LawfulApplicative G]

theorem traverse_nat {α}  (x : T α) (f : ApplicativeHom F G) (g : α → F β) :
      f (traverse g x) = traverse (f.fn ∘ g) x := by
let R := f.toApplicativeRel
apply LawfulTraversable.traverse_sim _ R; intro a
simp [ApplicativeHom.toApplicativeRel]

end nat

end LawfulTraversable
