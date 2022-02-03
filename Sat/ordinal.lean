import Lean.Elab.Command
import Lib.Logic.Classical

macro "obtain " p:term " from " d:term : tactic =>
  `(tactic| match $d:term with | $p:term => ?_)

-- macro "left" : tactic =>
--   `(tactic| apply Or.inl)

-- macro "right" : tactic =>
--   `(tactic| apply Or.inr)

-- macro "refl" : tactic =>
--   `(tactic| apply rfl)

-- macro "exfalso" : tactic =>
--   `(tactic| apply False.elim)

macro "byContradiction" h: ident : tactic =>
  `(tactic| apply Classical.byContradiction; intro h)

theorem swapHyp {p q : Prop} (h : p) (h' : ¬ p) : q := by
  cases h' h

macro "swapHyp" h:term "as" h':ident : tactic =>
  `(tactic| apply Classical.byContradiction; intro $h' <;>
            first
            | apply $h ; clear $h
            | apply swapHyp $h <;> clear $h
              )

-- open Lean Parser.Tactic Elab Command Elab.Tactic Meta
-- macro "fail" : tactic => pure $ throwError "foo"

namespace Option

@[simp]
theorem map_none {f : α → β} :
  Option.map f none = none := rfl

@[simp]
theorem map_some {f : α → β} {x} :
  Option.map f (some x) = some (f x) := rfl

attribute [simp] map_id

end Option

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

class WellOrdered (α : Type) where
  R : α → α → Prop
  wf : WellFounded R
  total x y : R x y ∨ x = y ∨ R y x

instance [WellOrdered α] : LT α := ⟨ WellOrdered.R ⟩
instance [WellOrdered α] : LE α where
  le x y := x = y ∨ x < y

namespace WellOrdered

variable [Hwo : WellOrdered α]

theorem le_of_lt {x y : α} : x < y → x ≤ y := Or.inr

theorem lt_irrefl (x : α) : ¬ x < x := by
have := WellOrdered.wf.apply x
induction this with | intro x h ih =>
intro h'
apply ih _ h' h'

theorem le_refl (x : α) : x ≤ x := by
  left; refl

theorem lt_antisymm {x y : α} :
  x < y → y < x → False := by
revert y
have := WellOrdered.wf.apply x
induction this with | intro x h ih =>
intros y Hxy Hyx
cases ih _ Hyx Hyx Hxy

theorem le_antisymm {x y : α} :
  x ≤ y → y ≤ x → x = y := by
intros Hxy Hyx; match x, Hxy, Hyx with
| x, Or.inl rfl, _ => intros; refl
| x, Or.inr Hx_lt, Or.inl rfl => refl
| x, Or.inr Hx_lt, Or.inr Hy_lt =>
  cases lt_antisymm Hx_lt Hy_lt


section
open Classical

theorem bottom_exists [inst : Nonempty α] :
  ∃ x : α, ∀ y : α, ¬ y < x := by
cases inst with | intro x =>
have h := Hwo.wf.apply x
induction h with | intro y h ih => exact
if h : ∃ z, z < y then by
  cases h with | intro z hz =>
  apply ih _ hz
else by
  rewrite [not_exists] at h
  exists y; assumption

noncomputable def bottom (α) [WellOrdered α]
  [inst : Nonempty α] : α :=
choose bottom_exists

theorem lt_iff_not_lt [h : WellOrdered α] (x y : α) :
  x < y ↔ ¬ y ≤ x := by
constructor
focus
  intros h₀ h₁
  match y, h₁ with
  | y, Or.inr h₁ =>
    apply lt_antisymm h₀ h₁
  | _, Or.inl rfl =>
    apply lt_irrefl _ h₀
focus
  intros h₀
  have := WellOrdered.total x y
  match y, this with
  | y, Or.inl h₀ => assumption
  | _, Or.inr (Or.inl rfl) =>
    exfalso
    apply h₀; clear h₀
    apply le_refl
  | y, Or.inr (Or.inr h₁) =>
    exfalso
    apply h₀; clear h₀
    right; assumption

theorem not_lt_bottom
  [inst : Nonempty α] :
  ¬ x < bottom α :=
choose_spec bottom_exists x

theorem bottom_le
  [inst : Nonempty α] :
  bottom α ≤ x := by
have H := not_lt_bottom (α := α) (x := x)
simp [lt_iff_not_lt] at H
assumption

end

theorem lt_trans {x y z : α} :
  x < y → y < z → x < z := by
rewrite [lt_iff_not_lt x z]
intros hxy hyz hxz
cases hxz with
| inl hxz =>
  subst hxz
  apply lt_antisymm hxy hyz
| inr hxz =>
  have := WellOrdered.wf.apply x
  induction this generalizing y z with | intro x h ih =>
  apply @ih _ hxz x y <;> assumption

theorem le_trans {x y z : α} :
  x ≤ y → y ≤ z → x ≤ z := by
intros hxy hyz
cases hxy with
| inl hxy =>
  cases hyz with
  | inl hyz => subst hxy hyz; left; refl
  | inr hyz => subst hxy; right; assumption
| inr hxy =>
  cases hyz with
  | inl hyz => subst hyz; right; assumption
  | inr hyz =>
    right; apply lt_trans
      <;> assumption

section Classical
open Classical

-- noncomputable
-- def max (x y : α) : α :=
-- if x < y
--   then y
--   else x

theorem max_le_iff (x y z : α) :
  max x y ≤ z ↔ x ≤ z ∧ y ≤ z := by
byCases Hyz : y < x
focus
  have := le_of_lt Hyz
  simp [max, *]
  constructor
  focus
    intros h
    constructor <;> try assumption
    apply le_trans <;> assumption
  focus
    intro h; cases h; assumption
focus
  simp [max, *]
  simp [lt_iff_not_lt] at Hyz
  constructor
  focus
    intros h
    constructor <;> try assumption
    apply le_trans <;> assumption
  focus
    intros h; cases h; assumption

end Classical
end WellOrdered

def WellOrder := Sigma WellOrdered

noncomputable
instance : CoeSort WellOrder (Type) := ⟨ Sigma.fst ⟩

instance (α : WellOrder) : WellOrdered α := α.snd

structure WellOrderHom (α β : WellOrder) where
  hom : α.1 → β.1
  hom_preserve x y : α.2.R x y → β.2.R (hom x) (hom y)

namespace WellOrderHom

instance : CoeFun (WellOrderHom a b) (λ _ => a → b) where
  coe f := f.hom

theorem ext {f g : WellOrderHom a b}
  (h : ∀ x, f x = g x) :
  f = g := by
have d : f.hom = g.hom := funext h
cases f with
| mk f hf =>
cases g with | mk g hg =>
  simp at d; revert hf hg;
  rewrite [d]; intros; exact rfl

theorem ext_iff {f g : WellOrderHom a b}
  (h : f = g) :
  ∀ x, f x = g x := by
subst h; intros; refl

def id : WellOrderHom α α where
  hom := _root_.id
  hom_preserve x y hxy := hxy

def comp (f : WellOrderHom β γ) (g : WellOrderHom α β) : WellOrderHom α γ where
  hom := f.hom ∘ g.hom
  hom_preserve x y hxy := f.hom_preserve _ _ (g.hom_preserve _ _ hxy)

variable {X Y Z W : WellOrder}
variable (f : WellOrderHom X Y)
variable (g : WellOrderHom Y Z)
variable (h : WellOrderHom Z W)

@[simp]
theorem id_comp : id.comp f = f := by apply ext; intro x; exact rfl
@[simp]
theorem comp_id : f.comp id = f := by apply ext; intro x; exact rfl
@[simp]
theorem comp_assoc : (h.comp g).comp f = h.comp (g.comp f) :=
by apply ext; intro x; exact rfl

end WellOrderHom

class IsMono {X Y} (f : WellOrderHom X Y) where
  mono : ∀ W (g₁ g₂ : WellOrderHom W X), f.comp g₁ = f.comp g₂ → g₁ = g₂

namespace IsMono
variable {X Y Z : WellOrder}
variable (f : WellOrderHom X Y)
variable (g : WellOrderHom Y Z)
variable (gZY : WellOrderHom Z Y)
variable (gZX : WellOrderHom Z X)
open WellOrderHom

instance : IsMono (@WellOrderHom.id X) where
  mono W g₁ g₂ := by simp; apply _root_.id

instance [IsMono f] [IsMono g] : IsMono (g.comp f) where
  mono W g₁ g₂ := by
    simp; intro h
    have h := mono _ _ _ h
    apply mono _ _ _ h

end IsMono

class IsIso {X Y} (f : WellOrderHom X Y) where
  inv : WellOrderHom Y X
  to_inv : f.comp inv = WellOrderHom.id
  inv_to : inv.comp f = WellOrderHom.id

export IsIso (inv)

namespace IsIso
attribute [simp] to_inv inv_to

open WellOrderHom
variable {X Y Z : WellOrder}
variable (f : WellOrderHom X Y)
variable (g : WellOrderHom Y Z)
variable (gZY : WellOrderHom Z Y)
variable (gZX : WellOrderHom Z X)

@[simp]
theorem to_inv_reassoc [IsIso f] :
  f.comp ((inv f).comp gZY) = gZY :=
by rw [← WellOrderHom.comp_assoc, to_inv, id_comp]

@[simp]
theorem inv_to_reassoc [IsIso f] :
  (inv f).comp (f.comp gZX) = gZX :=
by rw [← WellOrderHom.comp_assoc, inv_to, id_comp]

instance [IsIso f] : IsIso (inv f) where
  inv := f
  to_inv := inv_to
  inv_to := to_inv

instance : IsIso (@WellOrderHom.id X) where
  inv := id
  to_inv := by simp
  inv_to := by simp

instance [IsIso f] [IsIso g] : IsIso (g.comp f) where
  inv := (inv f).comp (inv g)
  to_inv := by simp
  inv_to := by simp

instance (priority := low) [IsIso f] : IsMono f where
  mono W g₁ g₂ Heq := by
    rw [← inv_to_reassoc f g₁, Heq, inv_to_reassoc]

end IsIso

section HasArrow
-- set_option checkBinderAnnotations false

inductive HasArrow X Y (cl : WellOrderHom X Y → Type u) : Prop :=
| intro (f : WellOrderHom X Y) : cl f → HasArrow X Y cl

end HasArrow

def WellOrderMono (α β : WellOrder) := HasArrow α β IsMono
@[matchPattern]
def WellOrderMono.intro (f : WellOrderHom x y) [IsMono f] :
  WellOrderMono x y :=
HasArrow.intro f inferInstance

def WellOrderIso (α β : WellOrder) := HasArrow α β IsIso
@[matchPattern]
def WellOrderIso.intro (f : WellOrderHom x y) [IsIso f] :
  WellOrderIso x y :=
HasArrow.intro f inferInstance

-- namespace WellOrderIso

-- variable {X Y : WellOrder}

-- def flip (f : WellOrderIso X Y) : WellOrderIso Y X where
--   to := f.inv
--   inv := f.to
--   to_inv := f.inv_to
--   inv_to := f.to_inv

-- def toMono (f : WellOrderIso X Y) : WellOrderMono X Y where
--   to := f.to
--   mono Z g₀ g₁ h := _

-- end WellOrderIso

-- inductive Erased (α : Type u) : Prop :=
-- | intro (x : α) : Erased α

-- theorem Erased_impl {α β} (f : α → β) : Erased α → Erased β
-- | ⟨ x ⟩ => ⟨ f x ⟩

def WOEqv (α β : WellOrder) : Prop :=
WellOrderIso α β

def Ordinal := Quot WOEqv

namespace Ordinal

protected def mk (α : Type) [WellOrdered α] : Ordinal :=
Quot.mk _ { fst := α, snd := inferInstance }

def zero : Ordinal :=
Quot.mk _
{ fst := Empty,
  snd :=
  { R := by {intro x; cases x},
    wf := by { constructor; intro x; cases x },
    total := by {intro x; cases x} } }

inductive Option.R (r : α → α → Prop) : Option α → Option α → Prop where
| top x : R r (some x) none
| lifted x y : r x y → R r (some x) (some y)

theorem Option.R_acc {r : α → α → Prop}
        x (h : Acc r x) : Acc (Option.R r) (some x) := by
  induction h with
  | intro y h' ih =>
    constructor; intros z Hr; cases Hr
    apply ih; assumption

theorem Option.R_wf {r : α → α → Prop}
        (h : WellFounded r) : WellFounded (Option.R r) := by
  constructor; intro x
  match x with
  | none =>
    constructor; intro y h'; cases h'
    apply Option.R_acc
    apply h.apply
  | some x =>
    apply Option.R_acc
    apply h.apply

instance [WellOrdered α] : WellOrdered (Option α) where
  R := Option.R (WellOrdered.R)
  wf := Option.R_wf (WellOrdered.wf)
  total := λ x y =>
    match x, y with
    | none, none => by
      apply Or.inr; apply Or.inl
      constructor
    | none, some _ => by
      apply Or.inr; apply Or.inr
      constructor
    | some _, none => by
      apply Or.inl
      constructor
    | some x, some y =>
      match WellOrdered.total x y with
      | Or.inl h =>
        Or.inl $ Option.R.lifted _ _ h
      | Or.inr (Or.inl h) =>
        Or.inr $ Or.inl $ congrArg _ h
      | Or.inr (Or.inr h) =>
        Or.inr $ Or.inr $ Option.R.lifted _ _ h

def impl.S : WellOrder → WellOrder
| ⟨α, Hα⟩ =>
  let _ : WellOrdered α := Hα
  { fst := Option α,
    snd := inferInstance }

def S_hom (h : WellOrderHom a b) :
    WellOrderHom (impl.S a) (impl.S b) where
  hom := Option.map h
  hom_preserve := by
    intros x y h; cases x <;>
      cases y <;>
      cases h <;>
      constructor <;>
      apply h.hom_preserve <;>
      assumption

@[simp]
theorem id_hom :
  (@WellOrderHom.id a).hom = id := rfl

@[simp]
theorem S_hom_hom (h : WellOrderHom a b) :
  (S_hom h).hom = Option.map h.hom := rfl

@[simp]
theorem comp_hom (f : WellOrderHom b c) (g : WellOrderHom a b) :
  (f.comp g).hom = f.hom ∘ g.hom := rfl

@[simp]
theorem comp_S_hom
  (f : WellOrderHom b c) (g : WellOrderHom a b) :
  (S_hom f).comp (S_hom g) = S_hom (f.comp g) :=
WellOrderHom.ext $ by
  intro x
  cases x <;> simp [WellOrderHom.comp, S_hom]

@[simp]
theorem S_hom_id {α} :
  S_hom (@WellOrderHom.id α) = WellOrderHom.id :=
WellOrderHom.ext $ by
  intro x
  rw [S_hom_hom, id_hom, id_hom]
  simp

instance [@IsIso x y f] : IsIso (S_hom f) where
  inv := S_hom (inv f)
  to_inv := by simp
  inv_to := by simp

def S_iso : WellOrderIso a b → WellOrderIso (impl.S a) (impl.S b)
| ⟨f, h⟩ =>
  have h' := h
  ⟨S_hom f, inferInstance⟩
  -- to := S_hom h.to
  -- inv := S_hom h.inv
  -- to_inv := by simp [h.to_inv]
  -- inv_to := by simp [h.inv_to]

def S : Ordinal → Ordinal :=
Quot.lift (Quot.mk _ ∘ impl.S) λ a b Heqv => by
  simp
  apply Quot.sound
  exact S_iso Heqv

def Le (x y : Ordinal) : Prop :=
Quot.liftOn₂ x y
  (λ x y => WellOrderMono x y)
  (by intros a b x f
      cases f with
      | intro f hf =>
      simp; apply propext
      constructor <;> intros g
      { cases g with
        | intro g hg =>
          have hf := hf
          have hg := hg
          exact ⟨g.comp (inv f), inferInstance⟩ }
      { cases g with
        | intro g hg =>
          have hf := hf
          have hg := hg
          exact ⟨g.comp f, inferInstance⟩ } )
  (by intros x a b f
      cases f with | intro f hf =>
      simp; apply propext
      constructor <;> intros g
      { cases g with
        | intro g hg =>
          have hf := hf
          have hg := hg
          exact ⟨f.comp g, inferInstance⟩ }
      { cases g with
        | intro g hg =>
          have hf := hf
          have hg := hg
          exact ⟨(inv f).comp g, inferInstance⟩ }
       )

def Lt (x y : Ordinal) : Prop :=
Le x y ∧ ¬ Le y x

-- structure StrictInclusion (a b : WellOrder) : Type where
--   inclusion : WellOrderHom a b
--   [incl_mono : IsMono inclusion]
--   strict : ¬ WellOrderMono b a

-- attribute [instance] StrictInclusion.incl_mono

instance : LE Ordinal := ⟨ Le ⟩
instance : LT Ordinal := ⟨ Lt ⟩

theorem le_refl (x : Ordinal) : x ≤ x := by
  cases x using Quot.ind
  simp [LE.le,Le]
  exists @WellOrderHom.id _
  exact inferInstance

infix:25 " ⟶ " => WellOrderHom

instance : WellOrdered Unit where
  R _ _ := False
  wf := ⟨ λ a => ⟨ _, by intros _ h; cases h ⟩ ⟩
  total := by intros; right; left; refl

def Unit : WellOrder := ⟨_root_.Unit,inferInstance⟩

def const {β : WellOrder} (x : β) : Unit ⟶ β where
  hom := λ i => x
  hom_preserve := by intros _ _ h; cases h

section inverse
open Classical
noncomputable
def inverse [Nonempty α] (f : α → β) (x : β) : α :=
epsilon λ y => f y = x

end inverse

section schroeder_bernstein
open Classical

def injective (f : α → β) : Prop :=
∀ x y, f x = f y → x = y

def surjective (f : α → β) : Prop :=
∀ y, ∃ x, f x = y

def bijective (f : α → β) : Prop :=
injective f ∧ surjective f

variable [Nonempty α] [Nonempty β]
variable (f : α → β) (hf : injective f)
variable (g : β → α) (hg : injective g)

theorem left_inv_of_injective :
  inverse f ∘ f = id := by
apply funext; intro x
simp [Function.comp, inverse]
apply hf
apply Classical.epsilon_spec (p := λ y => f y = f x)
exists x; refl

theorem right_inv_of_surjective (hf' : surjective f) :
  f ∘ inverse f = id := by
apply funext; intro x
specialize (hf' x)
apply Classical.epsilon_spec (p := λ y => f y = x)
assumption

theorem injective_of_left_inv
        (h : g ∘ f = id) :
  injective f := by
intros x y Hxy
have Hxy : (g ∘ f) x = (g ∘ f) y := congrArg g Hxy
rewrite [h] at Hxy; assumption

theorem injective_of_right_inv
        (h : g ∘ f = id) :
  surjective g := by
intros x
exists (f x)
show (g ∘ f) x = x
rewrite [h]; refl
-- def lonely (b : β) := ∀ a, f a ≠ b

-- def iterate (n : Nat) (b : β) : β :=
-- match n with
-- | 0 => b
-- | Nat.succ n => iterate n (f (g b))

-- -- #exit
-- def descendent (b₀ b₁ : β) : Prop :=
-- ∃ n, iterate f g n b₀ = b₁
-- -- #exit
-- theorem schroeder_bernstein :
--   ∃ h : α → β, bijective h := by
-- let p x y := lonely f y ∧ descendent f g y (f x)
-- let h x :=
--   if ∃ y, p x y
--     then inverse g x
--     else f x
-- exists h; constructor
-- focus
--   intro x y; simp
-- -- focus
-- --   intros x y
-- --   -- simp at Hxy
-- --   simp
-- -- --   have : (∃ z, p x z) ↔ (∃ z, p y z) := by
-- -- --     constructor <;> intros h
-- -- --     focus
-- -- --       cases h with
-- -- --       | intro z hz => unfold p at *
-- -- --   admit
--   byCases hx : (∃ z, p x z) <;>
--     byCases hy : (∃ z, p y z) <;>
--     simp [*] <;> intro h3
--   focus
--     clear h
--     cases hx with | intro x' hx' =>
--     cases hy with | intro y' hy' =>
--       cases hy'; cases hx'
--       clear p
-- admit
-- abort
-- -- match propDecidable (∃ z, p x z), propDecidable (∃ z, p y z), Hxy with
-- -- | isTrue ⟨x', hx, hx'⟩, isTrue ⟨y', hy, hy'⟩, Hxy => _
-- -- | isTrue _, isFalse _, Hxy => _
-- -- | isFalse _, isTrue _, Hxy => _
-- -- | isFalse _, isFalse _, Hxy => _
-- -- -- { admit }
-- --      simp [h] at Hxy }
-- -- exists (inverse g ∘ f)

end schroeder_bernstein

theorem comp_const (f : WellOrderHom a b) x :
  f.comp (const x) = const (f x) := rfl

theorem injective_of_monomorphism
        (f : WellOrderHom a b) [IsMono f] :
  injective f.hom := by
intros x y Hxy
have := @IsMono.mono _ _ f _ _ (const x) (const y)
simp [comp_const, Hxy] at this
have := WellOrderHom.ext_iff this ()
assumption

-- Need Schroeder-Bernstein Theorem
theorem le_antisymm (x y : Ordinal)
        (Hxy : x ≤ y)
        (Hyx : y ≤ x) : x = y := by
  cases x using Quot.ind
  cases y using Quot.ind
  simp [LE.le,Le] at *
  apply Quot.sound
  cases Hxy with | intro f hf =>
  cases Hyx with | intro g hg => _
  admit

theorem le_trans (x y z : Ordinal)
        (Hxy : x ≤ y)
        (Hyz : y ≤ z) : x ≤ z := by
  cases x using Quot.ind
  cases y using Quot.ind
  cases z using Quot.ind
  simp [LE.le,Le] at *
  cases Hxy with | intro f hf =>
  cases Hyz with | intro g hg =>
  have hf := hf
  have hg := hg
  exists g.comp f
  exact inferInstance

theorem lt_total (x y : Ordinal) :
  x < y ∨ x = y ∨ y < x := by
byCases hxy : (x ≤ y) <;>
  byCases hyx : (y ≤ x)
focus
  right; left
  apply le_antisymm <;> assumption
focus
  left; constructor <;> assumption
focus
  right; right
  constructor <;> assumption
focus
  admit
-- Todo:
-- Le is a total order
-- Limits
-- zero is a limit? (no)
-- zero, Succ, Limit are distinct
-- recursor / induction principle


namespace WellOrdered

variable  [WellOrdered α]

theorem le_iff_forall_le (x y : α) :
  x ≤ y ↔ ∀ z, y ≤ z → x ≤ z := by
constructor <;> intros h
focus
  intros z h'
  apply WellOrdered.le_trans <;> assumption
focus
  apply h
  apply WellOrdered.le_refl

theorem le_iff_forall_ge (x y : α) :
  x ≤ y ↔ ∀ z, z ≤ x → z ≤ y := by
constructor <;> intros h
focus
  intros z h'
  apply WellOrdered.le_trans <;> assumption
focus
  apply h
  apply WellOrdered.le_refl

theorem le_total (x y : α) :
  x ≤ y ∨ y ≤ x := sorry

section Classical
open Classical

theorem le_max_l {x y : α} :
  x ≤ max x y := by
rw [le_iff_forall_le]; intros z
rw [WellOrdered.max_le_iff]
intros h; cases h; assumption

theorem le_max_r {x y : α} :
  y ≤ max x y := by
rw [le_iff_forall_le]; intros z
rw [WellOrdered.max_le_iff]
intros h; cases h; assumption


instance : @Reflexive α LE.le where
  refl := WellOrdered.le_refl

theorem max_eq_of_le {x y : α} :
  x ≤ y → max x y = y := by
intros h
apply WellOrdered.le_antisymm
focus
  rw [WellOrdered.max_le_iff]
  auto
focus
  apply WellOrdered.le_max_r

theorem max_eq_of_ge {x y : α} :
  y ≤ x → max x y = x := by
intros h
apply WellOrdered.le_antisymm
focus
  rw [WellOrdered.max_le_iff]
  auto
focus
  apply WellOrdered.le_max_l

end Classical
end WellOrdered

noncomputable
instance : CoeSort WellOrder Type := ⟨ Sigma.fst ⟩

structure Seq where
  index : Type
  [wo : WellOrdered index]
  ords : index → WellOrder
  increasing (i j : index) : i ≤ j → ords i ⟶ ords j
  [mono (i j : index) h : IsMono (increasing i j h)]
  strict (i j : index) :
    i < j → ¬ WellOrderMono (ords i) (ords j)
  increasing_refl (i : index) h :
    increasing i i h =
    WellOrderHom.id
  increasing_trans (i j k : index) (h : i ≤ j) (h' : j ≤ k) :
    (increasing _ _ h').comp (increasing _ _ h) =
    increasing _ _ (WellOrdered.le_trans h h')
  bottom : index
  next : index → index
  infinite i : i < next i
  nothing_below_bottom x : ¬ x < bottom
  consecutive i j : j < next i → j < i ∨ j = i

attribute [instance] Seq.wo Seq.mono

-- theorem Seq.increasing' (i j : s.index) :
--   i ≤ j → ords i ⟶ ords j

theorem Seq.bottom_le (s : Seq) x : s.bottom ≤ x := by
  have := s.nothing_below_bottom x
  simp [WellOrdered.lt_iff_not_lt] at this
  assumption

def Lim.Eqv (s : Seq) :
  (Σ i : s.index, s.ords i) → (Σ i, s.ords i) → Prop
| ⟨i, x⟩, ⟨j, y⟩ =>
  (∃ h : i < j, s.increasing _ _ (WellOrdered.le_of_lt h) x = y) ∨
  (∃ h : i = j, cast (by rw [h]) x = y) ∨
  (∃ h : i > j, s.increasing _ _ (WellOrdered.le_of_lt h) y = x)

def Lim (s : Seq) :=
Quot (Lim.Eqv s)

namespace Lim

variable (s : Seq)

theorem Eqv.intro i j (h : i ≤ j)
        x y
        (h' : s.increasing i j h x = y) :
  Eqv s ⟨i, x⟩ ⟨j, y⟩ := by
cases h with
| inl h =>
  subst h; right; left
  exists @rfl _ i
  simp [cast]
  simp [Seq.increasing_refl, WellOrderHom.id] at h'
  assumption
| inr h =>
  left; exists h
  assumption

theorem cast_cast {a b} (h : a = b) (h' : b = a) x :
  cast h (cast h' x) = x := by
cases h; cases h'; refl

theorem Eqv.symm x y :
  Eqv s x y →
  Eqv s y x := by
intros h; cases h with
| inl h => right; right; assumption
| inr h =>
  cases h with
  | inl h =>
    right; left
    cases h with | intro h h' =>
    exists h.symm
    rewrite [← h', cast_cast]
    refl
  | inr h => left; assumption

section
open Classical

theorem Eqv.intro' i j Hi Hj
        x y
        (h' : s.increasing i (max i j) Hi x =
              s.increasing j (max i j) Hj y) :
  Eqv s ⟨i, x⟩ ⟨j, y⟩ := by
cases WellOrdered.le_total i j with
| inl h =>
  have h₂ := WellOrdered.max_eq_of_le h
  revert Hi Hj h'
  rewrite [h₂]; intros Hi Hj
  rewrite [s.increasing_refl j]; intros h'
  apply Eqv.intro; assumption
| inr h =>
  have h₂ := WellOrdered.max_eq_of_ge h
  revert Hi Hj h'
  rewrite [h₂]; intros Hi Hj
  rewrite [s.increasing_refl i]; intros h'
  apply Lim.Eqv.symm
  apply Eqv.intro
  apply Eq.symm; assumption

end

theorem EqvGen_Eqv x y :
  EqvGen (Eqv s) x y ↔ Eqv s x y := by
constructor <;> intros h
focus
  induction h with
  | @rfl a =>
    cases a
    right; left
    exists @rfl _ _; simp [cast]
  | @step x y z a _ b =>
    cases x
    cases y
    cases z

  | symm_step a => skip

end Lim

namespace Lim

variable (s : Seq)
open Classical

theorem mk_eq_mk_max_l i j x :
  Quot.mk (Lim.Eqv s) ⟨i, x⟩ =
  Quot.mk _ ⟨max i j, s.increasing i (max i j)
    WellOrdered.le_max_l x⟩ := by
rw [Quot.eq]
apply EqvGen.once;
  apply Eqv.intro
{ refl }

theorem mk_eq_mk_max_r i j x :
  Quot.mk (Lim.Eqv s) ⟨i, x⟩ =
  Quot.mk _ ⟨max j i, s.increasing i (max j i)
    WellOrdered.le_max_r x⟩ := by
rw [Quot.eq]
apply EqvGen.once;
  apply Eqv.intro
{ refl }

-- theorem mk_eq_mk_max_r i j x :
--   Quot.mk (Lim.Eqv s) ⟨i, x⟩ =
--   Quot.mk _ ⟨max j i, s.increasing i (max j i)

protected inductive R : Lim s → Lim s → Prop :=
| intro i (x y : s.ords i) :
  x < y → Lim.R (Quot.mk _ ⟨i, x⟩) (Quot.mk _ ⟨i, y⟩)

-- protected def SigmaT := PSigma (λ i => s.ords i)
-- protected def toSigma : Lim s → Lim.SigmaT s
-- | ⟨a,b,h⟩ => ⟨a,b⟩
-- protected def SigmaT.R : Lim.SigmaT s → Lim.SigmaT s → Prop :=
-- PSigma.Lex LT.lt (λ _ => LT.lt)

-- protected theorem SigmaT.R_Subrelation :
--   Subrelation (Lim.R s) (InvImage (SigmaT.R s) (Lim.toSigma s)) := by
--   intros x y h
--   cases h with
--   | same i j k =>
--     simp [InvImage, Lim.toSigma]
--     apply PSigma.Lex.right; assumption
--   | lt x y =>
--     cases x; cases y
--     constructor; assumption

protected theorem R_wf :
  WellFounded (Lim.R s) := by
-- Subrelation.wf _ (InvImage.wf _ _)
constructor; intro a
cases a using Quot.ind with | mk a =>
cases a with | mk a b =>
have Hacc := WellOrdered.wf.apply b
-- let f b := Quot.mk (Eqv s) { fst := a, snd := b }
-- have Hacc := InvImage.accessible f Hacc
-- apply Acc
induction Hacc with | intro b h ih =>
-- clear h
constructor; intros y
generalize Hx : (Quot.mk (Eqv s) { fst := a, snd := b }) = x
intros Hr
cases Hr with | intro i x =>
rw [Quot.eq] at Hx
-- cases Hr
-- apply ih
skip


-- let lex : WellFounded (Lim.SigmaT.R s) :=
  -- (PSigma.lex WellOrdered.wf (λ i => WellOrdered.wf))
-- Subrelation.wf
  -- (SigmaT.R_Subrelation s)
  -- (InvImage.wf (Lim.toSigma s) lex)

protected theorem R_total x y :
  Lim.R s x y ∨ x = y ∨ Lim.R s y x :=
match x, y with
| ⟨x,x',hx⟩, ⟨y,y',hy⟩ =>
  match x, y, WellOrdered.total x y with
  | _, _, Or.inl h => by left; constructor; assumption
  | _, _, Or.inr (Or.inr h) => by right; right; constructor; assumption
  | a, _, Or.inr (Or.inl rfl) =>
    match WellOrdered.total x' y' with
    | Or.inl h => by left; constructor; assumption
    | Or.inr (Or.inl h) => by subst h; right; left; refl
    | Or.inr (Or.inr h) => by right; right; constructor; assumption

instance : WellOrdered (Lim s) where
  R := Lim.R s
  wf := Lim.R_wf s
  total := Lim.R_total s

theorem exists_in_inclusion (h : StrictInclusion a b) :
  ∃ x : b, True := by
apply Classical.byContradiction; intro h₀
rewrite [Classical.not_exists] at h₀
apply h.strict
let f (x : b) : a := False.elim (h₀ x trivial)
refine' ⟨⟨f, _⟩,_⟩
focus
  intros x; cases h₀ x trivial
focus
  constructor
  intros W g₁ g₂ _
  apply WellOrderHom.ext; intro a
  cases h₀ (g₁ a) trivial

section
open Classical
-- #print prefix

theorem exists_in_inclusion' (h : StrictInclusion a b) :
  ∃ x : b, ∀ y, ¬ h.inclusion y = x := by
byCases Ha : Nonempty a
focus
  apply Classical.byContradiction; intro h₀
  simp at h₀
  apply h.strict
  -- revert Ha; intro Ha
  have : injective h.inclusion.hom := injective_of_monomorphism _
  let f : b → a := inverse h.inclusion.hom
  have hf : ∀ i, f (h.inclusion i) = i :=
    congrFun (left_inv_of_injective _ this)
  refine' ⟨⟨f, _⟩,_⟩
  focus
    intros x y Hxy
    have Hx := h₀ x
    have Hy := h₀ y
    have : ∀ α [WellOrdered α] (a b : α),
             WellOrdered.R a b ↔ a < b := λ _ _ _ _ => Iff.rfl
    cases Hx with | intro x' Hx =>
    cases Hy with | intro y' Hy =>
    rewrite [← Hx, ← Hy, hf, hf]
    rewrite [this, WellOrdered.lt_iff_not_lt] at *
    rewrite [← Hx, ← Hy] at Hxy
    intros Hxy'; apply Hxy; clear Hxy x y Hx Hy this
    cases Hxy' with
    | inl h => subst h; left; refl
    | inr h =>
      right; apply WellOrderHom.hom_preserve
      assumption
  focus
    constructor
    intros W g₁ g₂ Hg
    apply WellOrderHom.ext; intros x
    have Hg := WellOrderHom.ext_iff Hg x
    simp [WellOrderHom.hom, WellOrderHom.comp] at Hg
    have := right_inv_of_surjective
      (WellOrderHom.hom h.inclusion) h₀
    have := congrFun this; simp at this
    have Hg := congrArg h.inclusion.hom Hg
    rewrite [this, this] at Hg; assumption
focus
  have := exists_in_inclusion h
  cases this with | intro x =>
  exists x; intros y _
  apply Ha; clear Ha
  constructor; assumption

end
--   intros x; cases h₀ x trivial
-- focus
--   constructor
--   intros W g₁ g₂ _
--   apply WellOrderHom.ext; intro a
--   cases h₀ (g₁ a) trivial


-- if h₀ : Nonempty a then by
--   cases h₀ with | intro x =>
--   exists h.inclusion x
--   -- exact intro
--   trivial
-- else by
--   -- cases h with | ⟨h₀, h₁⟩ =>
--   apply Classical.byContradiction
--   rewrite [not_exists]; intros h₁
--   apply h.strict
--   constructor

noncomputable
def witness (x : StrictInclusion a b) : b :=
Classical.choose (exists_in_inclusion' x)

protected noncomputable def default : Lim s where
  idx := s.next s.bottom
  val := witness (s.increasing _ _ (s.infinite _))
  min_idx j x h  := by
    let f := s.increasing _ _ (s.infinite s.bottom)
    cases s.consecutive _ _ h with
    | inl h =>
      cases s.nothing_below_bottom _ h
    | inr h =>
      subst j
      intros h₀
      apply
        Classical.choose_spec
          (exists_in_inclusion' f) _ h₀

noncomputable
instance : Inhabited (Lim s) where
  default := Lim.default s

end Lim

def lim (s : Seq) : Ordinal :=
Quot.mk _
{ fst := Lim s,
  snd := inferInstance }

theorem WO_is_equiv : EqvGen WOEqv x y → WOEqv x y := by
  intro h
  induction h with
  | rfl => exact ⟨WellOrderHom.id, inferInstance⟩
  | step h₀ _ ih =>
    cases h₀ with | intro f h₀ =>
    cases ih with | intro g ih =>
    exists g.comp f
    have h₀ := h₀; have ih := ih
    exact inferInstance
  | symm_step h₀ _ ih =>
    cases h₀ with | intro f h₀ =>
    cases ih with | intro g ih =>
    have h₀ := h₀; have ih := ih
    exists g.comp (inv f)
    exact inferInstance

theorem zero_ne_succ (x : Ordinal) : zero ≠ S x := by
  intros h
  cases x using Quot.ind with | mk x =>
  cases x with | mk a b =>
  simp [S] at h
  have h := WO_is_equiv $ Quot.eq.1 h
  simp [impl.S] at h
  cases h with | intro a b =>
  have b := b
  have f := (inv a).hom none
  cases f

theorem succ_ne_self (x : Ordinal) : x ≠ S x := by
  intros h
  cases x using Quot.ind with | mk x =>
  cases x with | mk a Ha =>
  revert Ha h; intros Ha h
  let Ha' : WellOrdered (Option a) := inferInstance
  let Ha'' : LT (Option a) := instLT
  simp [S] at h
  have h := WO_is_equiv $ Quot.eq.1 h
  cases h with | intro f hf =>
  have hf := hf
  have f := inv f
  have hf := f.hom_preserve
  simp [WellOrdered.R] at hf
  suffices H : ∀ x : Option a, some (f x) < x → False by
    apply H none
    simp only [LT.lt]
    constructor
  intros x
  have Hacc : Acc LT.lt x := WellOrdered.wf.apply _
  induction Hacc with | intro x _ ih =>
  intros h'
  apply ih _ h'
  constructor
  apply f.hom_preserve (some (f x)) x h'

open Classical

theorem zero_ne_lim (s : Seq) : zero ≠ lim s := by
  intros h
  -- rewrite [Quot.eq] at h
  have h := WO_is_equiv $ Quot.eq.1 h
  cases h with | intro f hf =>
  revert hf; intros hf
  have f := inv f
  have hf := f.hom_preserve
  cases f Inhabited.default
-- TODO:
-- succ ≠ lim
-- 0 ≠ lim
-- recursor
-- Lemma no Ordinal between x and S x?
-- #check Le
-- set_option trace.simp_rewrite true

-- #check getLocal
-- #check Lean.Expr.fvar

-- set_option trace.Ma
-- set_option trace.Elab.definition true

theorem S_consecutive y :
  y ≤ x ∧ y < S x ∨ x < y ∧ S x ≤ y := by
match lt_total x y with
| Or.inl Hlt =>
  right
  refine' ⟨Hlt, _⟩
  cases Hlt with | intro Hle Hnot_ge =>
  cases x using Quot.ind with | mk x =>
  cases y using Quot.ind with | mk y =>
  simp [Le] at Hle Hnot_ge
  have :
         (¬ Nonempty (y → x)) ∨
         (∃ f : y → x, ¬ Nonempty (y ⟶ x)) ∨
         (∃ f : y ⟶ x, IsMono f → False) := by
    apply byContradiction; intros h₀
    apply Hnot_ge; clear Hnot_ge
    simp at h₀
    match h₀ with
    | ⟨⟨f⟩, h₁, h₂⟩ =>
      cases h₁ f with | intro g =>
      cases h₂ g with | intro z => -- weird pretty printing: not
                                  -- printing the type means that
                                  -- we're not giving the ∀ variable a
                                  -- name
      -- cases z
      -- clear h₁
      constructor; assumption
  match this with
  | Or.inl h₀ =>
    cases Hle with | intro f Hf =>
    revert Hf; intros Hf
    have : StrictInclusion x y := ⟨f, Hnot_ge⟩
    let w := Lim.witness this
    simp [LE.le, S, Le]
    have : x → False := by
      intros a
      let f (b : y) := a
      apply h₀; constructor; assumption
    let g (_ : impl.S x) := w
    -- have : IsMono g := by
      -- intros
    let g' : impl.S x ⟶ y := by
      refine' ⟨g, _⟩
      intros a b Hab
      cases Hab with
      | top h => cases this h
      | lifted h => cases this h
    have hg : IsMono g' := by
      constructor; intros W g₁ g₂ Hg
      apply WellOrderHom.ext; intros x
      cases g₁ x with
      | some x => cases this x
      | none =>
        cases g₂ x with
        | some x => cases this x
        | none => refl
    constructor; assumption
  | Or.inr (Or.inl ⟨f, h₀⟩) =>
    clear this
    swapHyp h₀ as h₁
    constructor
    exists f
    skip
  | Or.inr (Or.inr h₀) => skip

| Or.inr (Or.inl Heq) => _
| Or.inr (Or.inr Hgt) => _

theorem lt_lim (s : Seq) x :
  lim s ≤ x ↔ ∀ i, Ordinal.mk (s.ords i) ≤ x := by
constructor
focus
  intros h i
  cases x using Quot.ind with | mk x =>
  simp [lim, LE.le, Le] at h
  cases h with | intro a b =>
  skip
focus
  intros h
  admit

theorem lim_not_consecutive (s : Seq) x :
  x < lim s → ∃ y, x < y ∧ y < lim s := by
admit

theorem S_ne_lim (s : Seq) : S x ≠ lim s := by
admit
