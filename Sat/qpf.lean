
import Lib.Tactic
import Lib.Data.Quot
import Sat.CategoryTheory

open Nat

namespace Function

@[simp]
def applied (v : α) (f : α → β) := f v

variable {f : α → β} {g g' : β → γ} {h : γ → σ}

@[simp]
theorem id_comp : (_root_.id ∘ f) = f :=
by apply funext; intro; refl

@[simp]
theorem comp_id : (f ∘ _root_.id) = f :=
by apply funext; intro; refl

@[simp]
theorem comp_assoc : (h ∘ g) ∘ f = h ∘ (g ∘ f) :=
by apply funext; intro; refl

theorem comp_reassoc : g = g' → g ∘ f = g' ∘ f :=
by intros h; subst h; refl

end Function

inductive Fin' : Nat → Type
| ZFin {n} : Fin' (succ n)
| SFin {n} : Fin' n → Fin' (succ n)

inductive Vec (α : Type u) : Nat → Type u
| nil : Vec α 0
| cons {n} : α → Vec α n → Vec α (succ n)

namespace Vec

def mk {α} : {n : Nat} → (f : Fin' n → α) → Vec α n
| 0, f => Vec.nil
| succ n, f => Vec.cons (f $ Fin'.ZFin) (mk $ λ i => f $ Fin'.SFin i)

def apply {α} {n : Nat} : Vec α n → Fin' n → α
| Vec.cons x xs, Fin'.ZFin => x
| Vec.cons x xs, Fin'.SFin i => apply xs i

def map {α β} (f : α → β) : {n : Nat} → Vec α n → Vec β n
| 0, Vec.nil => Vec.nil
| _, Vec.cons x xs => Vec.cons (f x) (map f xs)

@[simp]
theorem map_id' {α} {n : Nat} v :
  Vec.map (n := n) (@id α) v = v := by
induction v with
| nil => refl
| cons x xs ih => simp [ih, map]

@[simp]
theorem map_id {α} {n : Nat} :
  Vec.map (n := n) (@id α) = id := by
apply funext; intros x
apply map_id'

@[simp]
theorem map_comp' {α β γ} (f : α → β) (g : β → γ) {n : Nat} v :
  Vec.map (n := n) g (Vec.map f v) = Vec.map (g ∘ f) v := by
simp [Function.comp]
induction v with
| nil => refl
| cons x xs ih => simp [ih, map]

@[simp]
theorem map_comp {α β γ} (f : α → β) (g : β → γ) {n : Nat} :
  Vec.map (n := n) g ∘ Vec.map f = Vec.map (g ∘ f) := by
apply funext; intros x
apply map_comp'

@[simp]
theorem apply_map {α β} (f : α → β) (v : Vec α n) i :
  (v.map f).apply i = f (v.apply i) := by
induction i <;>
  cases v <;> simp [map, apply, *]

@[simp]
theorem map_mk {α β} (f : α → β) (v : Fin' n → α) :
  ((Vec.mk v).map f) = Vec.mk (f ∘ v) := by
induction n <;>
  simp [map, mk, (·∘·), *]

@[simp]
theorem apply_mk {α} : ∀ {n : Nat} (f : Fin' n → α) (i : Fin' n),
  (mk f).apply i = f i
| _, f, Fin'.ZFin => rfl
| _, f, Fin'.SFin i => by simp [mk, apply, apply_mk]

def unapplied {f : α → Sort _} :
  {n : Nat} → {v : Vec α n} → {i : Fin' n} → (v.map f).apply i → f (v.apply i)
| _, Vec.cons x xs, Fin'.ZFin, a => a
| _, Vec.cons x xs, Fin'.SFin i, a => unapplied (v := xs) (i := i) a

def unapplied₂ {α β : Type _} {f : α → β → Sort _} {x} :
  {n : Nat} → {v : Vec α n} → {i : Fin' n} →
    (v.map f).apply i x →
    f (v.apply i) x
| _, Vec.cons x xs, Fin'.ZFin, a => a
| _, Vec.cons x xs, Fin'.SFin i, a => unapplied₂ (v := xs) (i := i) a

def applied {f : α → Sort _} :
  {n : Nat} → {v : Vec α n} → {i : Fin' n} → f (v.apply i) → (v.map f).apply i
| _, Vec.cons x xs, Fin'.ZFin, a => a
| _, Vec.cons x xs, Fin'.SFin i, a => applied (v := xs) (i := i) a

end Vec

def TypeVec := Vec (Type _)

namespace TypeVec
export Vec (nil cons)
end TypeVec

inductive TypeMap : {n : Nat} → TypeVec n → TypeVec n → Type _
| nil : TypeMap TypeVec.nil TypeVec.nil
| cons  {a b} {n : Nat} {xs ys : TypeVec n} :
  (a → b) → TypeMap xs ys → TypeMap (TypeVec.cons a xs) (TypeVec.cons b ys)

namespace TypeMap

protected def id : {n : Nat} → {v : TypeVec n} → TypeMap v v
| 0, TypeVec.nil => TypeMap.nil
| succ n, TypeVec.cons a xs => TypeMap.cons _root_.id TypeMap.id

def comp : {n : Nat} → {v₀ v₁ v₂ : TypeVec n} →
    TypeMap v₁ v₂ →
    TypeMap v₀ v₁ →
    TypeMap v₀ v₂
| 0, _, _, _, TypeMap.nil, TypeMap.nil => TypeMap.nil
| succ n, _, _, _, TypeMap.cons f fs, TypeMap.cons g gs =>
  TypeMap.cons (f ∘ g) (comp fs gs)

section Notations

local infixr:20 " ⟶ " => TypeMap
local infixr:60 " ⊚ " => TypeMap.comp
local notation "𝟙" => TypeMap.id
-- notation "𝟙_" => TypeMap.id

def apply {n} {v₀ v₁ : TypeVec n} : (v₀ ⟶ v₁) → (i : Fin' n) → v₀.apply i → v₁.apply i
| cons f fs, Fin'.ZFin, x => f x
| cons f fs, Fin'.SFin i, x => apply fs i x

def mk {n} : {v₀ v₁ : TypeVec n} → ((i : Fin' n) → v₀.apply i → v₁.apply i) → (v₀ ⟶ v₁)
| Vec.nil, Vec.nil, _ => TypeMap.nil
| Vec.cons x xs, Vec.cons y ys, f => TypeMap.cons (f Fin'.ZFin) (mk $ λ i => f $ Fin'.SFin i)

@[simp]
theorem apply_mk' {n} {v₀ v₁ : TypeVec n}
  (f : (i : Fin' n) → v₀.apply i → v₁.apply i) i :
  (mk f).apply i = f i := by
induction i with
| ZFin =>
  cases v₀; cases v₁
  simp [apply]
| SFin n ih =>
  cases v₀; cases v₁
  apply funext; intros v
  simp [apply, ih]

@[simp]
theorem apply_mk {n} {v₀ v₁ : TypeVec n}
  (f : (i : Fin' n) → v₀.apply i → v₁.apply i) :
  (mk f).apply = f := by
apply funext
apply apply_mk'

@[simp]
theorem mk_apply {n} {v₀ v₁ : TypeVec n}
  (f : v₀ ⟶ v₁) :
  mk f.apply = f := by
induction f with
| nil =>
  simp [apply]; refl
| cons f fs ih =>
  simp [apply]
  conv =>
    rhs
    rw [← ih]
  skip

@[simp]
theorem comp_id : ∀ {n : Nat} {v₀ v₁ : TypeVec n} (f : v₀ ⟶ v₁), f ⊚ 𝟙 = f
| 0, _,_, TypeMap.nil => rfl
| succ n, _,_, TypeMap.cons f fs => by
  simp [TypeMap.comp, @comp_id n]

@[simp]
theorem id_comp : ∀ {n : Nat} {v₀ v₁ : TypeVec n} (f : v₀ ⟶ v₁), 𝟙 ⊚ f = f
| 0, _,_, TypeMap.nil => rfl
| succ n, _,_, TypeMap.cons f fs => by
  simp [TypeMap.comp, @id_comp n]

@[simp]
theorem comp_assoc : ∀ {n : Nat} {v₀ v₁ v₂ v₃ : TypeVec n}
  (f : v₀ ⟶ v₁) (g : v₁ ⟶ v₂) (h : v₂ ⟶ v₃), (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f)
| 0, _, _, _, _, TypeMap.nil, TypeMap.nil, TypeMap.nil => rfl
| succ n, _, _, _, _, TypeMap.cons f fs, TypeMap.cons g gs, TypeMap.cons h hs => by
  simp [TypeMap.comp, @comp_assoc n]

end Notations

open category_theory

instance {n} : Category (TypeVec.{u} n) where
  hom := TypeMap
  id := TypeMap.id
  comp := TypeMap.comp
  id_comp := TypeMap.id_comp
  comp_id := TypeMap.comp_id
  assoc := TypeMap.comp_assoc

instance {n} : Category (Vec.{u+1} (Type u) n) :=
inferInstanceAs (Category (TypeVec n))

theorem comp_reassoc {n : Nat} {v₀ v₁ v₂ v₃ : TypeVec n}
  (f : v₀ ⟶ v₁) (g g' : v₁ ⟶ v₂) : g = g' → g ⊚ f = g' ⊚ f :=
by intros h; subst h; refl

protected def map {v₀ : Vec α n} {v₁ : Vec β n} (f : α → Type u) (g : β → Type u)
  (F : ∀ i, f (v₀.apply i) → g (v₁.apply i)) :
  Vec.map f v₀ ⟶ Vec.map g v₁ :=
match n, v₀, v₁, F with
| _, Vec.nil, Vec.nil, F => TypeMap.nil
| _, Vec.cons x xs, Vec.cons y ys, F =>
  TypeMap.cons (F Fin'.ZFin) (TypeMap.map f g $ λ i => F $ Fin'.SFin i)

@[simp]
protected def map_id {v₀ : Vec α n} (f : α → Type u) :
   TypeMap.map (v₀ := v₀) f f (λ i => 𝟙_ (f (Vec.apply v₀ i))) = 𝟙 := by
induction v₀ with
| nil => simp [TypeMap.map]; refl
| cons x xs ih => simp [TypeMap.map, ih]; refl

@[simp]
protected def map_comp {v₀ v₁ v₂ : Vec _ n}
  (f₀ : α₀ → Type u)
  (f₁ : α₁ → Type u)
  (f₂ : α₂ → Type u)
  (F₀ : ∀ i, f₀ (v₀.apply i) ⟶ f₁ (v₁.apply i))
  (F₁ : ∀ i, f₁ (v₁.apply i) ⟶ f₂ (v₂.apply i)) :
   TypeMap.map _ _ F₁ ⊚ TypeMap.map _ _ F₀ =
   TypeMap.map _ _ λ i => F₁ i ⊚ F₀ i := by
simp [(·⊚·)]
induction v₀
all_goals { cases v₁; cases v₂; simp [TypeMap.map, *, comp] }

end TypeMap
open category_theory

-- class NFunctor {n} (F : TypeVec n → Type u) where
--   map : {a b : TypeVec n} → (a ⟶ b) → F a → F b
--   map_id : ∀ {a : TypeVec n}, map (𝟙_ a) = id
--   map_comp : ∀ {a b c : TypeVec n} (f : a ⟶ b) (g : b ⟶ c),
--     (map g ∘ map f) = map (g ⊚ f)

-- attribute [simp] NFunctor.map_id NFunctor.map_comp

-- class NFunctor {n} (F : TypeVec n → Type u) where
--   map : {a b : TypeVec n} → (a ⟶ b) → F a → F b
--   map_id : ∀ {a : TypeVec n}, map (𝟙_ a) = id
--   map_comp : ∀ {a b c : TypeVec n} (f : a ⟶ b) (g : b ⟶ c),
--     (map g ∘ map f) = map (g ⊚ f)

-- attribute [simp] NFunctor.map_id NFunctor.map_comp
open category_theory
open category_theory.IsFunctor

namespace NFunctor

def set {n} (F : TypeVec (succ n) → Type u) (v : Type _) (vs : TypeVec n) : Type u :=
F $ TypeVec.cons v vs

namespace set
variable (F : TypeVec (succ n) → Type u) [IsFunctor F]

protected def map v (f : a ⟶ b) : set F v a ⟶ set F v b :=
show F (TypeVec.cons v a) ⟶ F (TypeVec.cons v b) from
let g : TypeVec.cons v a ⟶ TypeVec.cons v b :=
        TypeMap.cons _root_.id f
map (F := F) g

protected theorem map_id :
  set.map F v 𝟙 = @id (set F v a) :=
map_id

protected theorem map_comp {a b c : TypeVec n} (f : a ⟶ b) (g : b ⟶ c) :
  set.map F v g ⊚ set.map F v f = set.map F v (g ⊚ f) :=
by simp [set.map]; simp [(·⊚·), TypeMap.comp]

end set

instance (F : TypeVec (succ n) → Type u) [IsFunctor F] :
         IsFunctor (set F v) where
  map := set.map F v
  map_id := set.map_id F
  map_comp := set.map_comp F

-- def comp {n m}
--   (Gs : Vec (Sigma $ @NFunctor.{v} m) n)
--   (F : TypeVec.{v} n → Type u) (v : TypeVec m) : Type u :=
-- match n, Gs, F with
-- | 0, Vec.nil, F => F Vec.nil
-- | _, Vec.cons G Gs, F =>
--   comp Gs
--     (set F (G.1 v)) v
open Function (applied)

def comp {n m}
  (Gs : Vec (TypeVec.{u₂} m → Type u₁) n)
  (F : TypeVec.{u₁} n → Type u₀) (v : TypeVec m) : Type u₀ :=
F (Gs.map $ applied v)

namespace comp

protected def map {n m}
  (Gs : Vec (TypeVec.{u₂} m → Type u₁) n)
  [∀ i, IsFunctor $ Gs.apply i]
  (F : TypeVec.{u₁} n → Type u₀) [IsFunctor F]
  {v₀ v₁ : TypeVec m} (f : v₀ ⟶ v₁) :
  comp Gs F v₀ ⟶ comp Gs F v₁ :=
show F _ ⟶ F _ from
map (TypeMap.map _ _ $ λ i =>
  show Gs.apply i v₀ ⟶ Gs.apply i v₁ from
  map f)

variable
  (Gs : Vec (TypeVec.{u₂} m → Type u₁) n)
  [∀ i, IsFunctor $ Gs.apply i]
  (F : TypeVec.{u₁} n → Type u₀) [IsFunctor F]

protected theorem map_id {v₀ : TypeVec m} :
  comp.map Gs F 𝟙 = @id (comp Gs F v₀) := by
simp [comp.map]; refl

protected theorem map_comp {v₀ : TypeVec m} (f : v₀ ⟶ v₁) (g : v₁ ⟶ v₂) :
  comp.map Gs F g ⊚ comp.map Gs F f = comp.map Gs F (g ⊚ f) := by
simp [comp.map]
rewrite [TypeMap.map_comp]
simp

instance : IsFunctor (comp Gs F) where
  map := comp.map Gs F
  map_id := comp.map_id Gs F
  map_comp := comp.map_comp Gs F

end comp

end NFunctor

structure PFunctor (n : Nat) where
  A : Type u
  B : A → TypeVec.{u} n

namespace PFunctor

variable {n : Nat} (P : PFunctor.{u} n)

protected structure apply' (v : TypeVec.{u} n) : Type u where
mk_impl ::
  a : P.A
  b_pi : ∀ i, (P.B a).apply i → v.apply i

def apply := @PFunctor.apply'

namespace apply
variable {P}

protected def b {v} (x : PFunctor.apply P v) : P.B x.a ⟶ v :=
TypeMap.mk x.b_pi

@[matchPattern]
protected def mk {v} a (f : P.B a ⟶ v) : PFunctor.apply P v :=
PFunctor.apply'.mk_impl a f.apply

@[simp]
theorem a_mk {v} a (f : P.B a ⟶ v) :
  (apply.mk a f).a = a := rfl

@[simp]
theorem b_mk {v} a (f : P.B a ⟶ v) :
  (apply.mk a f).b = f :=
by simp [apply.mk, apply.b]


@[recursor 1]
def casesOn {motive : PFunctor.apply P v → Sort _}
  (x : P.apply v)
  (f : ∀ a b, motive (apply.mk a b)) :
  motive x := by
specialize f x.a x.b
simp [apply.mk, apply.b] at f
cases x; assumption

end apply

protected def map {a b : TypeVec n}
  (f : a ⟶ b) (x : P.apply a) : P.apply b :=
PFunctor.apply.mk x.a (f ⊚ x.b)
-- #exit

protected def map_id {a : TypeVec n} : PFunctor.map P 𝟙 = @id (P.apply a) := by
  apply funext
  intros x; cases x using apply.casesOn
  simp [PFunctor.map]; refl

protected def map_comp {a b c : TypeVec n} (f : a ⟶ b) (g : b ⟶ c) :
  PFunctor.map P g ∘ PFunctor.map P f = PFunctor.map P (g ⊚ f) := by
  apply funext
  intros x; cases x using apply.casesOn
  simp [PFunctor.map]; refl

instance : IsFunctor P.apply where
  map := PFunctor.map P
  map_id := PFunctor.map_id P
  map_comp := PFunctor.map_comp P

instance instNFunctorApplyApply {m} (v : Vec (PFunctor n) m) i :
  IsFunctor ((v.map PFunctor.apply).apply i) :=
match m, v, i with
| _, Vec.cons x xs, Fin'.ZFin =>
  inferInstanceAs (IsFunctor x.apply)
| _, Vec.cons x xs, Fin'.SFin i => instNFunctorApplyApply xs i

end PFunctor

open NFunctor
-- structure NatTrans (F : TypeVec n → Type u)
--           (G : TypeVec n → Type v)
--           [IsFunctor F] [IsFunctor G] where
--   trans v : F v → G v
--   naturality {v₀ v₁} (f : v₀ ⟶ v₁) :
--     map f ∘ trans v₀ = trans v₁ ∘ map f

-- infix:40 " ⟹ " => NatTrans

-- attribute [simp] NatTrans.naturality

-- namespace NatTrans

-- variable {F₀ F₁ F₂ F₃ : TypeVec n → _}
-- variable [NFunctor F₀] [NFunctor F₁] [NFunctor F₂] [NFunctor F₃]

-- @[simp]
-- theorem naturality_reassoc (f : F₀ ⟹ F₁) {α}
--         {v₀ v₁} (h : v₀ ⟶ v₁) (g : α → F₀ v₀) :
--   map h ∘ f.trans v₀ ∘ g = f.trans v₁ ∘ map h ∘ g := by
-- rw [← Function.comp_assoc, naturality, Function.comp_assoc]

-- protected def id : F₀ ⟹ F₀ where
--   trans v := id
--   naturality := by
--     intros v₀ v₁ f
--     apply funext; intros; refl

-- protected def comp (g : F₁ ⟹ F₂) (f : F₀ ⟹ F₁) : F₀ ⟹ F₂ where
--   trans v := g.trans v ∘ f.trans v
--   naturality := by intros; simp

-- infixr:60 " ⊗ " => NatTrans.comp

-- variable (f f' : F₀ ⟹ F₁) (g : F₁ ⟹ F₂) (h : F₂ ⟹ F₃)

-- protected theorem ext
--           (h : ∀ x, f.trans x = f'.trans x) :
--   f = f' := by
-- cases f; cases f'
-- simp; apply funext
-- apply h

-- @[simp]
-- theorem id_comp : (NatTrans.id ⊗ f) = f := by
-- apply NatTrans.ext; intros; refl

-- @[simp]
-- theorem comp_id : (f ⊗ NatTrans.id) = f := by
-- apply NatTrans.ext; intros; refl

-- @[simp]
-- theorem comp_assoc : (h ⊗ g) ⊗ f = h ⊗ (g ⊗ f) := by
-- apply NatTrans.ext; intros; refl

-- end NatTrans

-- structure Equiv (F G : TypeVec n → Type _)
--           [NFunctor F] [NFunctor G] where
--   to : F ⟹ G
--   inv : G ⟹ F
--   to_inv : to ⊗ inv = NatTrans.id
--   inv_to : inv ⊗ to = NatTrans.id

-- namespace Equiv

-- variable
--   {F G H J : TypeVec n → Type _}
--   [NFunctor F] [NFunctor G] [NFunctor H] [NFunctor J]

-- attribute [simp] Equiv.to_inv Equiv.inv_to

-- @[simp]
-- theorem to_inv_reassoc (f : Equiv F G) (g : H ⟹ G) :
--   f.to ⊗ f.inv ⊗ g = g :=
-- by rw [← NatTrans.comp_assoc, to_inv, NatTrans.id_comp]

-- @[simp]
-- theorem inv_to_reassoc (f : Equiv F G) (g : H ⟹ F) :
--   f.inv ⊗ f.to ⊗ g = g :=
-- by rw [← NatTrans.comp_assoc, inv_to, NatTrans.id_comp]

-- protected def id : Equiv F F where
--   to := NatTrans.id
--   inv := NatTrans.id
--   to_inv := by simp
--   inv_to := by simp

-- @[simp] protected theorem to_id : (@Equiv.id _ F _).to = NatTrans.id := rfl
-- @[simp] protected theorem inv_id : (@Equiv.id _ F _).inv = NatTrans.id := rfl

-- protected def comp (f : Equiv G H) (g : Equiv F G) :
--           Equiv F H where
--   to := f.to ⊗ g.to
--   inv := g.inv ⊗ f.inv
--   to_inv := by simp
--   inv_to := by simp

-- @[simp] protected theorem to_comp (f : Equiv G H) (g : Equiv F G) :
--   (f.comp g).to = f.to.comp g.to := rfl

-- @[simp] protected theorem inv_comp (f : Equiv G H) (g : Equiv F G) :
--   (f.comp g).inv = g.inv.comp f.inv := rfl

-- protected def symm (f : Equiv F G) : Equiv G F where
--   to := f.inv
--   inv := f.to
--   to_inv := f.inv_to
--   inv_to := f.to_inv

-- @[simp] protected theorem to_symm (f : Equiv F G) :
--   f.symm.to = f.inv := rfl

-- @[simp] protected theorem inv_symm (f : Equiv F G) :
--   f.symm.inv = f.to := rfl

-- protected theorem ext {f g : Equiv F G} :
--   f.to = g.to → f = g := by
-- cases f with | mk fto finv fto_inv finv_to =>
-- cases g with | mk gto ginv gto_inv ginv_to =>
-- simp; intros h
-- constructor; assumption
-- have : _ ⊗ _ = _ ⊗ _ := congrArg (λ x => ginv ⊗ x) fto_inv
-- rw [h, ← NatTrans.comp_assoc, ginv_to] at this
-- simp at this; assumption

-- @[simp]
-- theorem id_comp (f : Equiv F G) : Equiv.id.comp f = f :=
-- Equiv.ext $ by simp

-- @[simp]
-- theorem comp_id (f : Equiv F G) : f.comp Equiv.id = f :=
-- Equiv.ext $ by simp

-- @[simp]
-- theorem comp_assoc (f : Equiv F G) (g : Equiv G H) (h : Equiv H J) :
--   (h.comp g).comp f = h.comp (g.comp f) :=
-- Equiv.ext $ by simp

-- @[simp]
-- theorem symm_id : (@Equiv.id _ F _).symm = Equiv.id :=
-- Equiv.ext $ by simp

-- @[simp]
-- theorem symm_comp (f : Equiv F G) (g : Equiv G H) :
--   (g.comp f).symm = f.symm.comp g.symm :=
-- Equiv.ext $ by simp

-- @[simp]
-- theorem symm_symm (f : Equiv F G) :
--   f.symm.symm = f :=
-- Equiv.ext $ by simp

-- end Equiv

structure RelationF (F : TypeVec n → Type _) where
  get {v : TypeVec n} : F v → F v → Prop

structure RelationF.apply {F : TypeVec n → Type _} (R : RelationF F) {X v} (x y : X ⟶ F v) : Prop where
  get : ∀ i, R.get (x i) (y i)

instance {F : TypeVec n → Type _} : CoeFun (RelationF F) (λ _ => ∀ {X v} (x y : X ⟶ F v), Prop) where
  coe R {X v} f g := RelationF.apply R f g

class FunctorialRel (F : TypeVec n → Type _) [IsFunctor F] (R : RelationF F) where
  map {v₀ v₁} {X} (x y : X ⟶ F v₀) (f : v₀ ⟶ v₁) :
    R x y → R (map (F := F) f ⊚ x) (map (F := F) f ⊚ y)
#exit
namespace FunctorialRel
open IsFunctor
variable
  {F : TypeVec n → Type _} [IsFunctor F]
  (R : RelationF F) [FunctorialRel F R]

def map' {v₀ v₁} (x y : F v₀) (f : v₀ ⟶ v₁) :
    R.get x y →
    R.apply (IsFunctor.map f x) (IsFunctor.map f y) := by
intros H i
apply map; apply H

end FunctorialRel


def QuotF (F : TypeVec n → Type _)
          (R : RelationF F)
          (v : TypeVec n) : Type _ :=
Quot (@R v)

namespace QuotF

variable {F : TypeVec n → Type _} [IsFunctor F]
         (R : RelationF F) [FunctorialRel F R]

protected def mk {a b : TypeVec n} (f : a ⟶ b) : F a ⟶ QuotF F R b :=
Quot.mk _ ⊚ map f

protected def lift {a b : TypeVec n} (f : a ⟶ b)
              (Hf : ∀ {X} (g₀ g₁ : X ⟶ F a), ) :
  QuotF F R a ⟶ F b :=
Quot.lift (map f : F a ⟶ F b) _

protected def map (f : a ⟶ b) : QuotF F R a → QuotF F R b :=
Quot.lift (Quot.mk (FunctorialRel) ⊚ map f : _ → _) $ by
  intros x y Hxy
  have Hxy := FunctorialRel.map _ _ f Hxy
  simp [QuotF, Quot.eq]
  apply EqvGen.once; assumption

protected def map_id : QuotF.map F R 𝟙 = @id (QuotF F R a) :=
funext $ Quot.ind $ by intros; simp [QuotF.map]

protected def map_comp (f : a ⟶ b) (g : b ⟶ c) :
  QuotF.map F R g ∘ QuotF.map F R f = QuotF.map F R (g ⊚ f) :=
funext $ Quot.ind $
by intros; simp [QuotF.map]; rw [← NFunctor.map_comp]; refl

end QuotF

instance (F : TypeVec n → Type u) [NFunctor F]
         (R : RelationF F) [FunctorialRel F R] :
         NFunctor (QuotF F R) where
  map := QuotF.map F R
  map_id := QuotF.map_id F R
  map_comp := QuotF.map_comp F R

class IsPolynomial (F : TypeVec n → Type _) [NFunctor F] where
  P : PFunctor n
  P_equiv : Equiv F P.apply

namespace IsPolynomial

namespace comp

section P

variable (P : PFunctor.{u} n) (Ps : Fin' n → PFunctor.{u} m)
-- #check @Vec.map
-- def apply (v : TypeVec m) : ∃ x, P.apply (Ps.map $ λ p => p.apply v) = x := by
-- constructor
-- simp only [PFunctor.apply]

protected def P' : PFunctor.{u} m :=
⟨Σ a : P.A, (i : Fin' n) → (P.B a).apply i → (Ps i).A,
 λ ⟨a, Fb⟩ =>
 Vec.mk $ λ i =>
 Σ (j : Fin' n),
 Σ (b : (P.B a).apply j),
   ((Ps j).B $ Fb _ b).apply i
 ⟩
-- set_option pp.universes true
-- #check Ps
-- #exit
-- protected def doop (i : Fin' n) (v : TypeVec.{u} m) :
--   (Vec.map (Function.applied v) (Vec.map PFunctor.apply Ps)).apply i →
--   (Ps.apply i).apply v :=
-- λ a =>
-- Vec.unapplied₂ (Vec.unapplied a)

protected def to_trans (v : TypeVec.{u} m) :
  comp (Vec.mk $ PFunctor.apply ∘ Ps) P.apply v →
  (comp.P' P Ps).apply v
-- | PFunctor.apply.mk a b => _
| ⟨a, b⟩ =>
  ⟨ ⟨a,
    λ i x =>
      PFunctor.apply.a (Vec.unapplied $ b _ _)⟩,
    λ i  =>
        _
 -- (comp.doop _ _ _ (b j k)).2 _ h'.2.2
⟩

#check comp.to_trans

theorem to_trans_mk (v : TypeVec m) (a : P.A) f :
  comp.to_trans P Ps v (PFunctor.apply.mk a f) =
  PFunctor.apply.mk (Sigma.mk a _) _  := _

-- #exit

protected def to : comp (Vec.map PFunctor.apply Ps) P.apply ⟹ (comp.P' P Ps).apply where
  trans := comp.to_trans P Ps
  naturality := by
    intros
    apply funext; intros x
    cases x using PFunctor.apply.casesOn
    simp [Function.comp]
    simp [comp.to_trans, map, PFunctor.map, NFunctor.comp, PFunctor.apply.b]

end P

variable
  (Gs : Vec (TypeVec.{u} m → Type u) n)
  [∀ i, NFunctor (Gs.apply i)]
  [HG : ∀ i, IsPolynomial (Gs.apply i) ]
  (F : TypeVec.{u} n → Type u) [@NFunctor n F] [IsPolynomial F]

protected def P : PFunctor.{u} m :=
comp.P' (P F) $ λ i => P (Gs.apply i)

namespace P_equiv

def to : comp Gs F ⟹ (comp.P Gs F).apply where
  trans v := _ ∘ (@P_equiv _ F _ _).to.trans _
  naturality := _

def inv : (comp.P Gs F).apply ⟹ comp Gs F := _

end P_equiv

def P_equiv : Equiv (comp Gs F) (PFunctor.apply (comp.P Gs F)) where
  to := _
  inv := _
  to_inv := _
  inv_to := _

instance : IsPolynomial (comp Gs F) where
  P := comp.P Gs F
  P_equiv := _

end comp

end IsPolynomial

class QPF (F : TypeVec n → Type u) [NFunctor F] where
  inner : TypeVec n → Type u
  [inner_Functor : NFunctor inner]
  [inner_isPoly : IsPolynomial inner]
  R : RelationF inner
  [R_functorial : FunctorialRel inner R]
  equiv : Equiv F (QuotF inner R)

attribute [instance] QPF.inner_Functor QPF.inner_isPoly QPF.R_functorial

namespace QPF
variable  (F : TypeVec n → Type u) [NFunctor F] [QPF F]

def abs {v} : inner F v → F v := equiv.inv.trans _ ∘ Quot.mk _

theorem abs_nat {v₀ v₁} (f : v₀ ⟶ v₁) :
map f ∘ abs F = abs F ∘ map f := by
  simp [abs]; simp only [Function.comp]
  apply funext; intros x
  apply congrArg; simp [map, QuotF.map]


end QPF

-- Todo:
-- Preserved under
-- composition
-- (co)fixpoint
-- quotient
