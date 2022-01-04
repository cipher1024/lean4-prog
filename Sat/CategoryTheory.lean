
-- TODO:
-- * implement ext, simps, reassoc
-- * Can reassoc be implemented as an overload of keyword `theorem`?
--   no solution found. Use attribute for now
--   can we customize the simp attribute? Preprocessing?
-- * structure / instance skeleton synthesis

import Lib.Tactic

namespace category_theory

class Category (C : Type u) where
  hom : C → C → Type v
  id {X} : hom X X
  comp {X Y Z} : hom Y Z → hom X Y → hom X Z
  id_comp {X Y} (f : hom X Y) : comp id f = f
  comp_id {X Y} (f : hom X Y) : comp f id = f
  assoc {W X Y Z} (f : hom W X) (g : hom X Y) (h : hom Y Z) :
    comp (comp h g) f = comp h (comp g f)

attribute [simp] Category.id_comp Category.comp_id Category.assoc

open Category
-- #exit
scoped infix:30 " ⟶ " => hom
scoped infixr:60 " ⊚ " => comp
scoped notation "𝟙" => Category.id
set_option quotPrecheck false
scoped notation "𝟙_" arg:70 => (@Category.id _ _ arg)
set_option quotPrecheck true

structure Cat where
  Obj : Type u
  inst : Category.{u,v} Obj

instance : CoeSort Cat.{u,v} (Type u) where
  coe := Cat.Obj

instance (C : Cat.{u,v}) : Category.{u,v} C := Cat.inst _

structure Functor (C D : Sort _) [Category.{u,v} C] [Category.{u',v'} D] where
  obj : C → D
  map {X Y : C} : X ⟶ Y → obj X ⟶ obj Y
  map_id {X : C} : map (𝟙_ X) = 𝟙
  map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map g ⊚ map f = map (g ⊚ f)

attribute [simp] Functor.map_id Functor.map_comp

scoped infix:30 " ⇒ " => Functor
namespace Functor

variable {C D E F}
  [Category.{u,v} C] [Category.{u₁,v₁} D]
  [Category.{u₂,v₂} E]
  [Category.{u₃,v₃} F]

instance : CoeFun (C ⇒ D) (λ _ => C → D) where
  coe := Functor.obj

def Id : C ⇒ C where
  obj := id
  map := id
  map_id := by intros; refl
  map_comp := by intros; refl

def comp (G : D ⇒ E) (F : C ⇒ D) : C ⇒ E where
  obj X := G $ F X
  map {X Y} f := G.map $ F.map f
  map_id := by intros; simp
  map_comp := by intros; simp

local infix:60 " ⊙ " => comp

@[simp]
theorem map_comp_reassoc {F : C ⇒ D} {W} {X Y Z : C}
        (h : W ⟶ F X)
        (f : X ⟶ Y) (g : Y ⟶ Z) :
    (F.map g ⊚ F.map f ⊚ h) = F.map (g ⊚ f) ⊚ h :=
by rw [← Category.assoc, F.map_comp]

@[simp]
theorem id_comp (f : C ⇒ D) : Id ⊙ f = f := by
cases f; refl

@[simp]
theorem comp_id (f : C ⇒ D) : f ⊙ Id = f := by
cases f; refl

@[simp]
theorem comp_assoc (f : C ⇒ D) (g : D ⇒ E) (h : E ⇒ F) : (h ⊙ g) ⊙ f = h ⊙ (g ⊙ f) := by
cases f; cases g; cases h
simp only [comp]
refl

@[simp]
theorem comp_map (f : C ⇒ D) (g : D ⇒ E)
        {X Y} (h : X ⟶ Y) :
  (g ⊙ f).map h = g.map (f.map h) := rfl

end Functor

scoped infixr:60 " ⊙ " => Functor.comp

instance : Category Cat.{u,v} where
  hom C D := Functor C D
  id {X} := @Functor.Id X _
  comp := Functor.comp
  id_comp := Functor.id_comp
  comp_id := Functor.comp_id
  assoc := Functor.comp_assoc

class IsFunctor {C D}
      [Category.{u,v} C]
      [Category.{u',v'} D] (F : C → D) where
  map {X Y} (f : X ⟶ Y) : F X ⟶ F Y
  map_id {X} : map (𝟙_ X) = 𝟙
  map_comp {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map g ⊚ map f = map (g ⊚ f)

attribute [simp] IsFunctor.map_id IsFunctor.map_comp

namespace IsFunctor

variable
 {C D} [Category C] [Category D]

def toFunctor (F : C → D) [IsFunctor F] : C ⇒ D where
  obj := F
  map := map
  map_id := map_id
  map_comp := map_comp

instance (F : C ⇒ D) : IsFunctor (F : C → D) where
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

end IsFunctor

structure NatTrans {C D} [Category.{u,v} C] [Category.{u',v'} D] (F G : C ⇒ D) where
  trans (X : C) : F X ⟶ G X
  naturality {X Y} (f : X ⟶ Y) :
    trans Y ⊚ F.map f = G.map f ⊚ trans X

scoped infix:30 " ⟹ " => NatTrans

attribute [simp] NatTrans.naturality

namespace NatTrans

variable {C D}
  [Category.{u,v} C]
  [Category.{u',v'} D]

variable
  {F G H J : C ⇒ D}

@[simp]
theorem naturality_reassoc (H : NatTrans F G) {W} {X Y : C} (f : X ⟶ Y) (g : W ⟶ F X) :
  H.trans Y ⊚ F.map f ⊚ g = G.map f ⊚ H.trans X ⊚ g :=
by rw [← Category.assoc, naturality, Category.assoc]

def ID : F ⟹ F where
  trans {_} := id
  naturality := by intros; simp

@[simp]
theorem trans_ID X :
  (ID (F := F)).trans X = id (C := D) := rfl

def comp (f : G ⟹ H) (g : F ⟹ G) : F ⟹ H where
  trans X := f.trans _ ⊚ g.trans _
  naturality := by intros; simp

local infixr:60 " ⊛ " => comp

@[simp]
theorem trans_comp (f : G ⟹ H) (g : F ⟹ G) X :
  (comp f g).trans X = f.trans X ⊚ g.trans X := rfl

protected theorem ext {f g : F ⟹ G}
          (h : ∀ X, f.trans X = g.trans X) :
  f = g :=
by cases f; cases g; simp; apply funext; intro; simp [*]

@[simp]
theorem id_comp (f : F ⟹ G) : ID ⊛ f = f :=
NatTrans.ext $ by intros; simp

@[simp]
theorem comp_id (f : F ⟹ G) : f ⊛ ID = f :=
NatTrans.ext $ by intros; simp

@[simp]
theorem comp_assoc (f : F ⟹ G) (g : G ⟹ H) (h : H ⟹ J) : (h ⊛ g) ⊛ f = h ⊛ (g ⊛ f) :=
NatTrans.ext $ by intros; simp

end NatTrans

instance {C D} [Category.{u,v} C] [Category.{u',v'} D] :
         Category (C ⇒ D) where
  hom := NatTrans
  id := NatTrans.ID
  comp := NatTrans.comp
  id_comp := NatTrans.id_comp
  comp_id := NatTrans.comp_id
  assoc := NatTrans.comp_assoc

namespace NatTrans

variable {C} [Category.{u,v} C]
variable {D} [Category.{u',v'} D]

@[simp]
theorem trans_comp' {F₀ F₁ F₂ : C ⇒ D}
        (f : F₀ ⟶ F₁) (g : F₁ ⟶ F₂) X :
  g.trans X ⊚ f.trans X = (g ⊚ f).trans X := rfl

@[simp]
theorem trans_comp'_reassoc {F₀ F₁ F₂ : C ⇒ D}
        (f : F₀ ⟶ F₁) (g : F₁ ⟶ F₂) X Y (h : Y ⟶ F₀ X) :
  g.trans X ⊚ f.trans X ⊚ h = (g ⊚ f).trans X ⊚ h :=
by rw [← assoc, trans_comp']

@[simp]
theorem trans_id (F : C ⇒ D) X :
  (𝟙_ F).trans X = 𝟙 := rfl

end NatTrans

instance : Category (Type u) where
  hom X Y := X → Y
  id {X} := id
  comp {X Y Z} f g := f ∘ g
  id_comp {X Y} f := funext λ x => rfl
  comp_id {X Y} f := funext λ x => rfl
  assoc := by intros; apply funext; intros; refl

instance {T₀ T₁ : Type _} : CoeFun (T₀ ⟶ T₁) (λ _ => T₀ → T₁) where
  coe := id

class IsIso {C} [Category C] {X Y : C} (f : X ⟶ Y) where
  inv : Y ⟶ X
  to_inv : f ⊚ inv = 𝟙
  inv_to : inv ⊚ f = 𝟙

attribute [simp] IsIso.to_inv IsIso.inv_to

namespace IsIso

variable {C} [Category C] {X Y Z : C}
variable (f : X ⟶ Y) [IsIso f]

@[simp]
theorem inv_to_reassoc (g : Z ⟶ X) :
  inv f ⊚ f ⊚ g = g := by
rw [← assoc, inv_to, id_comp]

@[simp]
theorem to_inv_reassoc (g : Z ⟶ Y) :
  f ⊚ inv f ⊚ g = g := by
rw [← assoc, to_inv, id_comp]

instance : IsIso (𝟙_ X) where
  inv := 𝟙
  to_inv := by simp
  inv_to := by simp

instance {f : X ⟶ Y} {g : Y ⟶ Z} [IsIso f] [IsIso g] :
         IsIso (g ⊚ f) where
  inv := IsIso.inv f ⊚ IsIso.inv g
  to_inv := by simp
  inv_to := by simp

end IsIso

structure Iso {C} [Category C] (X Y : C) where
  to : X ⟶ Y
  inv : Y ⟶ X
  to_inv : to ⊚ inv = 𝟙
  inv_to : inv ⊚ to = 𝟙

attribute [simp] Iso.to_inv Iso.inv_to

scoped infix:30 " ≃ " => Iso

namespace Iso

variable {C} [Category C] {X Y Z : C}
variable {D} [Category D]
variable {E} [Category E]
-- variable {f : Iso X Y}

-- @[simp]
-- theorem inv_to_reassoc (g : Z ⟶ X) :
--   inv f ⊚ f ⊚ g = g := by
-- rw [← assoc, inv_to, id_comp]

-- @[simp]
-- theorem to_inv_reassoc (g : Z ⟶ Y) :
--   f ⊚ inv f ⊚ g = g := by
-- rw [← assoc, to_inv, id_comp]

def ofHom (f : X ⟶ Y) [IsIso f] : Iso X Y where
  to := f
  inv := IsIso.inv (f := f)
  to_inv := IsIso.to_inv
  inv_to := IsIso.inv_to

instance (f : X ≃ Y) : IsIso f.to where
  inv := f.inv
  to_inv := by simp
  inv_to := by simp

def id : X ≃ X :=
ofHom 𝟙

def comp (f : Y ≃ Z) (g : X ≃ Y) : X ≃ Z :=
ofHom $ f.to ⊚ g.to

theorem ext (f g : X ≃ Y) (h : f.to = g.to) : f = g := by
cases f; cases g; simp at *
next to inv to_inv inv_to =>
next to' inv' to_inv' inv_to' =>
  have : _ ⊚ _ = _ ⊚ _ := congrArg (. ⊚ inv) inv_to'
  rw [assoc, h, to_inv] at this
  simp at this
  auto

section compCongr'
variable {f f' f'' : C ⇒ D} {g g' g'' : D ⇒ E}
def compCongr'
    (hf : f ⟶ f') (hg : g ⟶ g') :
    g ⊙ f ⟶ g' ⊙ f' where
  trans X := hg.trans _ ⊚ g.map (hf.trans _)
  naturality X := by simp

@[simp]
theorem compCongr'_trans
    (hf : f ⟶ f') (hg : g ⟶ g') X :
    (compCongr' hf hg).trans X =
    hg.trans _ ⊚ g.map (hf.trans _) := rfl

@[simp]
theorem compCongr'_comp
    (hf : f ⟶ f') (hg : g ⟶ g')
    (hf' : f' ⟶ f'') (hg' : g' ⟶ g'') :
    (compCongr' hf' hg') ⊚ compCongr' hf hg =
    compCongr' (hf' ⊚ hf) (hg' ⊚ hg) :=
NatTrans.ext $ λ X => by
simp [- NatTrans.trans_comp', - Functor.map_comp]
simp only [← NatTrans.trans_comp', ← Functor.map_comp]
simp [- NatTrans.trans_comp', - Functor.map_comp]

end compCongr'

def compCongr {f f' : C ⇒ D} {g g' : D ⇒ E}
    (hf : f ≃ f') (hg : g ≃ g') :
    g ⊙ f ≃ g' ⊙ f' where
  to := compCongr' hf.to hg.to
  inv := compCongr' hf.inv hg.inv
  to_inv := NatTrans.ext $
    by intros; simp
  inv_to := NatTrans.ext $
    by intros; simp

end Iso

structure Equiv (C D) [Category C] [Category D] where
  to : C ⇒ D
  inv : D ⇒ C
  to_inv : to ⊙ inv ≃ Functor.Id
  inv_to : inv ⊙ to ≃ Functor.Id

structure Eqv where
  C : Type u
  [cat : Category C]

attribute [instance] Eqv.cat

namespace Eqv

def hom (X Y : Eqv) : Type _ :=
Equiv X.1 Y.1

local infix:30 " ⟶ " => hom

variable {X Y : Eqv}
-- #exit

section reassoc

variable {Z} [Category Z]

theorem to_inv_reassoc' (f : X ⟶ Y) (g : Z ⇒ Y.C) :
  (f.to ⊙ f.inv) ⊙ g ≃ Functor.Id ⊙ g :=
Iso.compCongr Iso.id f.to_inv
  -- inv_to : inv ⊙ to ≃ Functor.Id
-- #exit

theorem to_inv_reassoc (f : X ⟶ Y) (g : Z ⇒ Y.C) :
  (f.to ⊙ f.inv ⊙ g) ≃ g := by
rw [← Functor.comp_assoc]
apply Iso.comp _ (to_inv_reassoc' _ _)
rw [Functor.id_comp]
exact Iso.id

end reassoc

def id : X ⟶ X where
  to := Functor.Id
  inv := Functor.Id
  to_inv := by simp; apply Iso.ofHom 𝟙
  inv_to := by simp; apply Iso.ofHom 𝟙

variable {Z : Eqv}

-- def comp (f : Y ⟶ Z) (g : X ⟶ Y) : X ⟶ Z where
--   to := f.to ⊙ g.to
--   inv := g.inv ⊙ f.inv
--   to_inv := by simp
--   inv_to := _

end Eqv

-- instance : Category Eqv where
--   hom := _
--   id := _
--   comp := _
--   id_comp := _
--   comp_id := _
--   assoc := _

scoped infix:30 " ≅ " => Equiv

instance {C D} [Category C] [Category D] : Category (C × D) where
  hom X Y := (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id {X} := (𝟙, 𝟙)
  comp {X Y Z}
    | ⟨f,f'⟩, ⟨g,g'⟩ => (f ⊚ g, f' ⊚ g')
  id_comp := by intro _ _ f; cases f; simp
  comp_id := by intro _ _ f; cases f; simp
  assoc {W X Y Z}
    | ⟨f,f'⟩, ⟨g,g'⟩, ⟨h,h'⟩ => by simp

end category_theory
