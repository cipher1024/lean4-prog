
-- TODO:
-- implement ext, simps, reassoc
-- Can reassoc be implemented as an overload of keyword `theorem`?
-- no solution found. Use attribute for now
-- can we customize the simp attribute?

import Sat.Tactics

namespace category_theory

class Category (C : Sort u) where
  hom : C → C → Sort v
  id {X} : hom X X
  comp {X Y Z} : hom Y Z → hom X Y → hom X Z
  id_comp {X Y} (f : hom X Y) : comp id f = f
  comp_id {X Y} (f : hom X Y) : comp f id = f
  assoc {W X Y Z} (f : hom W X) (g : hom X Y) (h : hom Y Z) :
    comp (comp h g) f = comp h (comp g f)

attribute [simp] Category.id_comp Category.comp_id Category.assoc

open Category

scoped infix:30 " ⟶ " => hom
scoped infixr:60 " ⊚ " => comp
scoped notation "𝟙" => Category.id

structure Cat where
  Obj : Sort u
  inst : Category.{u,v} Obj

instance : CoeSort Cat.{u,v} (Sort u) where
  coe := Cat.Obj

instance (C : Cat.{u,v}) : Category.{u,v} C := Cat.inst _

structure Functor (C D : Sort _) [Category.{u,v} C] [Category.{u',v'} D] where
  obj : C → D
  map {X Y : C} : X ⟶ Y → obj X ⟶ obj Y
  map_id {X : C} : map (id (X := X)) = Category.id
  map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map g ⊚ map f = map (g ⊚ f)

attribute [simp] Functor.map_id Functor.map_comp

scoped infix:30 " ⇒ " => Functor
namespace Functor

variable {C D E F}
  [Category.{u,v} C] [Category.{u₁,v₁} D]
  [Category.{u₂,v₂} E]
  [Category.{u₃,v₃} F]

def Id : C ⇒ C where
  obj := id
  map := id
  map_id := by intros; refl
  map_comp := by intros; refl

def comp (G : D ⇒ E) (F : C ⇒ D) : C ⇒ E where
  obj X := G.obj $ F.obj X
  map {X Y} f := G.map $ F.map f
  map_id := by intros; simp
  map_comp := by intros; simp

local infix:60 " ⊙ " => comp

@[simp]
theorem map_comp_reassoc {F : C ⇒ D} {W} {X Y Z : C}
        (h : W ⟶ F.obj X)
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

end Functor

scoped infix:60 " ⊙ " => Functor.comp

instance : Category Cat.{u,v} where
  hom C D := Functor C D
  id {X} := @Functor.Id X _
  comp := Functor.comp
  id_comp := Functor.id_comp
  comp_id := Functor.comp_id
  assoc := Functor.comp_assoc

structure NatTrans {C D} [Category.{u,v} C] [Category.{u',v'} D] (F G : C ⇒ D) where
  trans (X : C) : F.obj X ⟶ G.obj X
  naturality {X Y} (f : X ⟶ Y) : trans Y ⊚ F.map f = G.map f ⊚ trans X

scoped infix:30 " ⟹ " => NatTrans

attribute [simp] NatTrans.naturality

namespace NatTrans

variable {C D}
  [Category.{u,v} C]
  [Category.{u',v'} D]

variable
  {F G H J : C ⇒ D}

@[simp]
theorem naturality_reassoc (H : NatTrans F G) {W} {X Y : C} (f : X ⟶ Y) (g : W ⟶ F.obj X) :
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

instance : Category (Type u) where
  hom X Y := X → Y
  id {X} := id
  comp {X Y Z} f g := f ∘ g
  id_comp {X Y} f := funext λ x => rfl
  comp_id {X Y} f := funext λ x => rfl
  assoc := by intros; apply funext; intros; refl

class IsIso {C} [Category C] {X Y : C} (f : X ⟶ Y) where
  inv : Y ⟶ X
  to_inv : f ⊚ inv = 𝟙
  inv_to : inv ⊚ f = 𝟙

structure Iso {C} [Category C] (X Y : C) where
  to : X ⟶ Y
  inv : Y ⟶ X
  to_inv : f ⊚ inv = 𝟙
  inv_to : inv ⊚ f = 𝟙

scoped infix:30 " ≃ " => Iso

structure Equiv (C D) [Category C] [Category D] where
  to : C ⇒ D
  inv : D ⇒ C
  to_inv : to ⊙ inv ≃ Functor.Id
  inv_to : inv ⊙ to ≃ Functor.Id

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
