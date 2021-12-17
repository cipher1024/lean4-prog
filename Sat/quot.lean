-- #exit
import Sat.Tactics

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

def liftOn₂ (x : Quot r) (y : Quot r') (f : α → α' → β)
  (h : ∀ (a b : α) (a' : α'),
    r a b → f a a' = f b a')
  (h' : ∀ (a : α) (a' b' : α'),
    r' a' b' → f a a' = f a b') : β :=
Quot.liftOn x
  (λ x => Quot.liftOn y (f x) $
    by intros; apply h'; assumption) $
  by intros
     induction y using Quot.inductionOn
     simp [Quot.liftOn]
     apply h; assumption

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
