-- TODO: generate point-free lemmas
-- use registerSimpAttr to create simp rewrite sets

import Lib.Algebra.Monoid
import Lib.Data.Foldable
import Lib.Data.Functor
import Lib.Function

class Traversable (T : Type u → Type u) extends Functor T, Foldable T where
  traverse {F : Type u → Type u} [Applicative F] (f : α → F β) : T α → F (T β)
  mapM {F : Type u → Type u} [Monad F] (f : α → F β) : T α → F (T β)

namespace Traversable
end Traversable

open Traversable

def StateT.mk {σ α} (f : σ → m (α × σ)) : StateT σ m α := f

section Accum

variable {T : Type u → Type u} [Traversable T]
variable {α β : Type u} (f : α → σ → β × σ)

def accuml (x₀ : σ) (x : T α) : T β × σ :=
StateT.run (m := Id) (mapM (StateT.mk.{u,u} ∘ f) x) x₀

def scanl (x₀ : σ) (x : T α) : T β :=
StateT.run' (m := Id) (mapM (StateT.mk.{u,u} ∘ f) x) x₀

def accumr (x₀ : σ) (x : T α) : T β × σ :=
StateT.run (m := Id) (Op1.run (traverse (Op1.mk.{u,u} ∘ StateT.mk.{u,u} ∘ f) x)) x₀

def scanr (x₀ : σ) (x : T α) : T β :=
accumr f x₀ x |>.1

end Accum


section AccumIdx

variable {T : Type u → Type u} [Traversable.{u} T]
variable {α β : Type u} (f : Nat → α → σ → β × σ)

def accumlIdx (x₀ : σ) (x : T α) : T β × σ :=
accuml (λ a (x, i) => f i a x |>.map id (., i+1)) (x₀, 0) x |>.map id Prod.fst

def scanlIdx (x₀ : σ) (x : T α) : T β :=
accumlIdx f x₀ x |>.fst

end AccumIdx

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
    Comp.run (traverse (Comp.mk ∘ Functor.map f ∘ g) x) =
    traverse f <$> traverse g x
  foldl_eq_traverse {α β} (f : β → α → β) (x : T α) (x₀ : β) :
    Foldable.foldl f x₀ x =
    Endo.run (Op.run (Const.run (traverse
      (Const.mk (α := α) ∘ Op.mk ∘ Endo.mk ∘ flip f) x))) x₀
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

theorem Id.run_map {α β} (f : α → β) (x : Id α) :
  Id.run (f <$> x) = f (Id.run x) := rfl

section LawfulTraversable_of_hom

open Foldable LawfulTraversable Functor
open LawfulFoldable
variable {T₀} [Traversable T₀] [LawfulTraversable T₀]
variable {T₁} [Traversable T₁] [LawfulFoldable T₁]
              [LawfulFunctor T₁]

variable {f : {α : Type u} → T₁ α → T₀ α}
variable {g : {α : Type u} → T₀ α → T₁ α}
variable (Hinj : ∀ {α}, LeftInv (@f α) g)
variable (Hinj' : ∀ {α}, RightInv (@f α) g)
variable (Hmap : ∀ {α β} (x : T₁ α) (g : α → β),
               f (g <$> x) = g <$> f x)
variable (HmapConst : ∀ {α β} (x : T₁ α) (g : β),
               f (mapConst g x) = mapConst g (f x))
variable (Hfoldl : ∀ {α β} (x : T₁ α) (g : β → α → β) x₀,
               foldl g x₀ x = foldl g x₀ (f x))
variable (Hfoldr : ∀ {α β} (x : T₁ α) (g : α → β → β) x₀,
               foldr g x₀ x = foldr g x₀ (f x))
variable (Htraverse_f :
  ∀ {α β m} [Applicative m] (x : T₁ α) (g : α → m β),
               f <$> traverse g x = traverse g (f x))
variable (HmapM :
  ∀ {α β m} [Monad m] (x : T₁ α) (g : α → m β),
               f <$> mapM g x = mapM g (f x))

private theorem Htraverse_g {α β m} [Applicative m] [LawfulFunctor m]
        (x : T₀ α) (f : α → m β) :
  g <$> traverse f x = traverse f (g x) :=
Functor.Injective_map (Hinj.toHasLeftInv) _ _ $ by
rw [map_comp, Hinj', id_map, Htraverse_f, Hinj'.apply]

-- abbrev Map (F) [Functor F] (f : α → β) : F α → F β := map f

-- theorem Map_eq  (F) [Functor F] (f : α → β) : map f = Map F f := rfl

def LawfulTraversable_of_hom : LawfulTraversable T₁ where
  map_eq_traverse := by
    intros
    apply Injective_of_LeftInv Hinj
    rw [← Id.run_map f]
    simp [Hmap, Htraverse_f, map_eq_traverse, -Id.map_eq]
  foldr_eq_foldMap := foldr_eq_foldMap
  foldl_eq_traverse := by
    intros
    rw [Hfoldl, foldl_eq_traverse, ← Htraverse_f, Const.run_map]
  -- map_const := by
  --   intros; ext; simp only [(.∘.), HmapConst]
  --   -- apply Functor.Injective_map
  --   apply Injective_of_LeftInv Hinj
  --   simp [Hmap, HmapConst, map_const]
  -- id_map := by
  --   intros
  --   apply Injective_of_LeftInv Hinj
  --   simp [Hmap]
  -- comp_map := by
  --   intros
  --   apply Injective_of_LeftInv Hinj
  --   simp [Hmap]
  foldl_sim := foldl_sim
  toArray_toList := toArray_toList
  length_toList := length_toList
  foldl_toList := foldl_toList
  traverse_eq_mapM := by
    intros
    apply Functor.Injective_map (f := f)
    . apply HasLeftInv.intro; auto
    simp [HmapM, Htraverse_f, traverse_eq_mapM]
  comp_traverse := by
    intros α β γ F G; intros
    have : ∀ β x (y : G (F β)),
         Comp.run x = y ↔ x = Comp.mk y :=
      by intros; refl
    rw [this]
    apply Functor.Injective_map (f := f) Hinj.toHasLeftInv
    simp only [Htraverse_f, comp_traverse, Comp.map_mk]
    rw [← this, comp_traverse, ← Htraverse_f]
    simp only [map_comp]
    congr; ext;
    simp [(.∘.), Htraverse_f]
  traverse_sim x R := by
    intros
    rw [← Hinj.apply x]
    rw [← Htraverse_g Hinj Hinj' Htraverse_f]
    rw [← Htraverse_g Hinj Hinj' Htraverse_f]
    apply R.naturality; auto [traverse_sim]

end LawfulTraversable_of_hom

-- #exit
