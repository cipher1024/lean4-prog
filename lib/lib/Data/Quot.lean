
import Lib.Tactic

inductive EqvGen (R : α → α → Prop) : α → α → Prop :=
| rfl {x} : EqvGen R x x
| step {x y z} : R x y → EqvGen R y z → EqvGen R x z
| symm_step {x y z} : R y x → EqvGen R y z → EqvGen R x z

namespace EqvGen

variable {R : α → α → Prop}

theorem once (h : R x y) : EqvGen R x y := EqvGen.step h EqvGen.rfl
theorem once_symm (h : R y x) : EqvGen R x y := EqvGen.symm_step h EqvGen.rfl

theorem trans : EqvGen R x y → EqvGen R y z → EqvGen R x z := by
  intros h₀ h₁
  induction h₀ with
  | rfl => exact h₁
  | step hR hGen IH => exact step hR (IH h₁)
  | symm_step hR hGen IH => exact symm_step hR (IH h₁)

theorem symm_step_r : EqvGen R x y → R z y → EqvGen R x z := by
  intros h₀ h₁
  have h₁ := once_symm h₁
  apply trans <;> assumption
theorem step_r : EqvGen R x y → R y z → EqvGen R x z := by
  intros h₀ h₁
  have h₁ := once h₁
  apply trans <;> assumption

theorem symm : EqvGen R x y → EqvGen R y x := by
  intros h
  induction h with
  | rfl => exact rfl
  | step hR hGen IH => exact trans IH (symm_step hR rfl)
  | symm_step hR hGen IH => exact trans IH (step hR rfl)

end EqvGen

namespace Quot
variable {r : α → α → Prop}
variable {r' : α' → α' → Prop}

def map (f : α → α') (hf : ∀ x y, r x y → r' (f x) (f y)) : Quot r → Quot r' :=
Quot.lift (λ a => Quot.mk _ (f a)) $ by
  intros; apply Quot.sound; auto

def toQuotEqvGen : Quot r → Quot (EqvGen r) :=
map id $ λ x y => EqvGen.once

def liftOn₂ (x : Quot r) (y : Quot r') (f : α → α' → β)
  (h : ∀ (a b : α) (a' : α'),
    r a b → f a a' = f b a')
  (h' : ∀ (a : α) (a' b' : α'),
    r' a' b' → f a a' = f a b') : β :=
Quot.liftOn x
  (λ x => Quot.liftOn y (f x) $
    by intros; auto) $
  by intros
     induction y using Quot.inductionOn
     simp [Quot.liftOn]; auto

@[simp]
def liftOn₂_beta {x : α} {y : α'} (f : α → α' → β)
  (h : ∀ (a b : α) (a' : α'),
    r a b → f a a' = f b a')
  (h' : ∀ (a : α) (a' b' : α'),
    r' a' b' → f a a' = f a b') :
liftOn₂ (Quot.mk _ x) (Quot.mk _ y) f h h' = f x y :=
by simp [liftOn₂]

noncomputable def out (x : Quot r) : α :=
Classical.choose (exists_rep x)

theorem eq' : Quot.mk r x = Quot.mk r y ↔ EqvGen r x y := by
  constructor
  focus
    intros h
    have Hlift : ∀ (a b : α), r a b → EqvGen r x a = EqvGen r x b := by
      intros a b Hab
      apply propext
      constructor <;> intro h
      focus apply EqvGen.step_r <;> assumption
      focus apply EqvGen.symm_step_r <;> assumption
    rw [← Quot.liftBeta (r := r) (EqvGen r x) Hlift, ← h,
          Quot.liftBeta (r := r) _ Hlift]
    exact EqvGen.rfl
  focus
    intros h
    induction h with
    | rfl => refl
    | step Hr Hgen IH =>
      rw [← IH]
      apply Quot.sound; assumption
    | symm_step Hr Hgen IH =>
      apply Eq.symm
      rw [← IH]
      apply Quot.sound; assumption

theorem eq : Quot.mk r x = Quot.mk r y ↔ EqvGen r x y := by
  constructor
  focus
    intros h
    rewrite [← liftOn₂_beta (r:=r) (r':=r) (EqvGen r), h, liftOn₂_beta]
    focus
      exact EqvGen.rfl
    focus
      intros x y z Hxy
      apply propext
      constructor <;> intro h
      focus apply EqvGen.symm_step <;> assumption
      focus apply EqvGen.step <;> assumption
    focus
      intros x y z Hxy
      apply propext
      constructor <;> intro h
      focus apply EqvGen.step_r <;> assumption
      focus apply EqvGen.symm_step_r <;> assumption
  focus
    intros h
    induction h with
    | rfl => refl
    | step Hr Hgen IH =>
      rw [← IH]
      apply Quot.sound; assumption
    | symm_step Hr Hgen IH =>
      apply Eq.symm
      rw [← IH]
      apply Quot.sound; assumption

end Quot

attribute [auto] Quot.sound

def Relation1 (F : Type u → Type v) :=
{{α : Type u}} → F α → F α → Prop

class Relation1.Functorial {F} [Functor F] (R : Relation1 F) where
  rel_map {α β} (x y : F α) (f : α → β) : R x y → R (f <$> x) (f <$> y)

attribute [auto] Relation1.Functorial.rel_map

class Relation1.Applicative {F} [H : Applicative F] (R : Relation1 F)
      extends Relation1.Functorial R where
  refl {α} (x : F α) : R x x
  rel_pure {α : Type u} (x : α) : R (pure x) (pure x)
  rel_seq {α β : Type u} (x y : Unit → F α) (f g : F (α → β)) :
    R f g →
    R (x ()) (y ()) →
    R (Seq.seq f x) (Seq.seq g y)
  rel_map {α β : Type u} (x y : F α) (f : α → β) :=
    λ HR : R x y =>
    suffices R (pure f <*> x) (pure f <*> y) by simp [*]
    rel_seq _ _ _ _ (rel_pure _) HR

instance  {F} [Applicative F] (R : Relation1 F) [Relation1.Applicative R] :
          Reflexive (@R α) where
  refl := Relation1.Applicative.refl

attribute [auto] Relation1.Applicative.rel_pure Relation1.Applicative.rel_seq

def Quot1 {F} (R : Relation1 F) (α : Type u) := Quot (@R α)

namespace Quot1

variable {F : Type u → Type v} (R : Relation1 F)
variable {G : Type u → Type v} (R' : Relation1 G)

@[matchPattern]
def mk {α} (x : F α) : Quot1 R α :=
Quot.mk _ x

variable {R} {R'}

@[recursor 3]
def lift {α β} (f : F α → β) (h : ∀ x y : F α, R x y → f x = f y) : Quot1 R α → β :=
Quot.lift f h

section lift₂

def lift₂ {α β γ} (f : F α → G β → γ)
    (hF : ∀ x y : F α, ∀ z, R x y → f x z = f y z)
    (hG : ∀ x y : G β, ∀ z, R' x y → f z x = f z y) :
  Quot1 R α → Quot1 R' β → γ :=
λ x y =>
Quot.liftOn₂ x y f
  (λ x y z => hF _ _ _)
  (λ x y z => hG _ _ _)

def liftOn₂ {α β γ}
    (x : Quot1 R α) (y : Quot1 R' β)
    (f : F α → G β → γ)
    (hF : ∀ x y : F α, ∀ z, R x y → f x z = f y z)
    (hG : ∀ x y : G β, ∀ z, R' x y → f z x = f z y) : γ :=
lift₂ _ hF hG x y

end lift₂

@[simp]
theorem lift_mk  {α β} (f : F α → β) (x : F α) h :
  lift f h (mk R x) = f x :=
Quot.liftBeta _ h x

@[auto]
theorem sound (x y : F α) : R x y → mk R x = mk R y :=
Quot.sound

theorem ind {α} {β : Quot1 R α → Prop} (f : ∀ x, β (mk R x)) : ∀ x, β x :=
Quot.ind f

section Functorial
variable [Functor F]
variable [R.Functorial]

instance : Functor (Quot1 R) where
  map f := Quot1.lift (Quot1.mk _ ∘ (f <$> .)) $ by auto with 6

end Functorial

section Applicative
variable [Applicative F] [LawfulApplicative F]
variable [R.Applicative]

instance : Applicative (Quot1 R) where
  pure x := Quot1.mk _ (pure x)
  seq f x := Quot1.liftOn₂ f (x ())
    (λ f x => Quot1.mk R (f <*> x))
    ( by auto with 7 )
    ( by auto with 7 )

end Applicative

end Quot1
