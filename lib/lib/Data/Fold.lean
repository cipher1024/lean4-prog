
import Lib.Data.Array.Basic
import Lib.Data.Foldable
import Lib.Data.Prod.Basic
import Lib.Data.Profunctor
import Lib.Data.Quot
import Lib.Data.Traversable

import Lib.Equiv
import Lib.Tactic

structure FoldImpl (α β : Type u) where
  γ : Type u
  x₀ : γ
  f : γ → α → γ
  out : γ → β

open Profunctor

instance : Profunctor FoldImpl where
  dimap f g
    | ⟨ γ, x₀, step, out ⟩ => ⟨ γ, x₀, λ a => step a ∘ f, g ∘ out ⟩

instance : LawfulProfunctor FoldImpl where
  dimap_id x := by
    cases x; simp [dimap]
    repeat constructor
  dimap_comp f f' g g' x := by
    cases x; simp [dimap]
    repeat constructor

namespace FoldImpl

-- inductive R : FoldImpl α β → FoldImpl α β → Prop
-- | intro {γ γ' x₀ y₀ f g out out'} :
--   (Heq : Equiv γ γ') →
--   Heq.to x₀ = y₀ →
--   (∀ x y, g (Heq.to x) y = Heq.to (f x y)) →
--   (∀ x, out x = out' (Heq.to x)) →
--   R ⟨γ, x₀, f, out⟩ ⟨γ', y₀, g, out'⟩

inductive R : FoldImpl α β → FoldImpl α β → Prop
| intro {γ γ' x₀ y₀ f g out out'} (SIM : γ → γ' → Prop) :
  SIM x₀ y₀ →
  (∀ x x' y, SIM x x' → SIM (f x y) (g x' y)) →
  (∀ x x', SIM x x' → out x = out' x') →
  R ⟨γ, x₀, f, out⟩ ⟨γ', y₀, g, out'⟩

namespace R

variable {x y z : FoldImpl α β}

theorem refl : R x x := by
cases x
refine' ⟨(.=.), _, _, _⟩
<;> intros
<;> substAll <;> refl

instance : Reflexive (@R α β) := ⟨ @refl _ _ ⟩

local infixr:60 " ⊚ " => Equiv.comp

def rel.comp {α β γ} (r : α → β → Prop) (s : β → γ → Prop) x y := ∃ z, r x z ∧ s z y
def rel.flip {α β} (r : α → β → Prop) x y := r y x

local infixr:60 " ∘' " => rel.comp

theorem trans (Hxy : R x y) (Hyz : R y z) : R x z := by
cases Hxy with | intro Heq hxy₀ hxy₁ hxy₂ =>
next out₀ out₂ =>
cases Hyz with | intro Heq' hyz₀ hyz₁ hyz₂ =>
next out₁ =>
refine' ⟨(Heq ∘' Heq'), _, _, _⟩
. constructor <;> auto
focus
  intros; next a =>
  cases a; next a b =>
  cases b; next b₀ b₁ =>
  constructor; constructor
  . apply hxy₁; assumption
  . apply hyz₁; assumption
focus
  intros; next a =>
  cases a; next a b =>
  cases b; next b₀ b₁ =>
  trans (out₂ a);
  . apply hxy₂; assumption
  . apply hyz₂; assumption

theorem symm (Hxy : R x y) : R y x := by
cases Hxy with | intro Heq a b c =>
next out₀ out₁ =>
refine' ⟨rel.flip Heq, _, _, _⟩
<;> intros
<;> simp [*]
. assumption
. apply b; assumption
. rw [c]; assumption

end R

@[inline]
def foldl {F} [Foldable F] : (f : FoldImpl α β) → (ar : F α) → β
| ⟨γ, x₀, f, out⟩, ar => out <| Foldable.foldl f x₀ ar

@[inline]
def scanl {F} [Traversable F] : (f : FoldImpl α β) → (ar : F α) → F β
| ⟨γ, x₀, f, out⟩, ar => _root_.scanl (λ a y => (out y, f y a)) x₀ ar

@[inline]
def accuml {F} [Traversable F] : (f : FoldImpl α β) → (ar : F α) → F β × β
| ⟨γ, x₀, f, out⟩, ar =>
  Prod.map id out $ _root_.accuml (λ a y => (out y, f y a)) x₀ ar

@[inline]
def foldr {F} [Foldable F] : (f : FoldImpl α β) → (ar : F α) → β
| ⟨γ, x₀, f, out⟩, ar => out <| Foldable.foldr (flip f) x₀ ar

def accumr {F} [Traversable F] : (f : FoldImpl α β) → (ar : F α) → F β × β
| ⟨γ, x₀, f, out⟩, ar =>
  Prod.map id out $ _root_.accumr (λ a y => (out y, f y a)) x₀ ar

instance : Functor (FoldImpl α) where
  map f x := { x with out := f ∘ x.out }

@[simp]
theorem x₀_map {α β γ} (x : FoldImpl α β) (f : β → γ) :
  (f <$> x).x₀ = x.x₀ := rfl

@[simp]
theorem f_map {α β γ} (x : FoldImpl α β) (f : β → γ) :
  (f <$> x).f = x.f := rfl

@[simp]
theorem out_map {α β γ} (x : FoldImpl α β) (f : β → γ) :
  (f <$> x).out = f ∘ x.out := rfl

instance : Applicative (FoldImpl.{u} α) where
  pure x := ⟨ PUnit, ⟨ ⟩, λ x _ => x, λ _ => x ⟩
  seq {β γ} f x :=
      let x := x ();
         { γ := f.γ × x.γ,
           x₀ := (f.x₀, x.x₀),
           f := λ ⟨a,b⟩ z => ⟨f.f a z, x.f b z⟩,
           out := λ ⟨a, b⟩ => f.out a <| x.out b
          }

@[simp]
theorem x₀_seq {α β γ : Type _} (f : FoldImpl α (β → γ)) (x : FoldImpl α β) :
  (f <*> x).x₀ = (f.x₀, x.x₀) := rfl

@[simp]
theorem f_seq {α β γ : Type _} (f : FoldImpl α (β → γ)) (x : FoldImpl α β) :
  (f <*> x).f = (λ (a, b) i => (f.f a i, x.f b i)) := rfl

@[simp]
theorem out_seq {α β γ : Type _} (f : FoldImpl α (β → γ)) (x : FoldImpl α β) :
  (f <*> x).out = (λ (i, j) => f.out i $ x.out j) := rfl

end FoldImpl

def Fold (α β : Type _) := Quot (@FoldImpl.R α β)

namespace Fold

variable {α α' β β'} (f : α' → α) (g : β → β')

protected def dimap : Fold α β → Fold α' β' :=
Quot.lift (Quot.mk _ ∘ dimap f g) $ by
    intros x y h; simp; apply Quot.sound
    cases h with | intro SIM h₀ h₁ h₂ =>
    simp [dimap]
    refine' ⟨SIM, _, _, _⟩
    . assumption
    . intros; simp [(.∘.)]; auto
    intros; simp [(.∘.)]; congr
    auto

instance : Profunctor Fold where
  dimap := Fold.dimap

instance : LawfulProfunctor Fold where
  dimap_id x := by
    cases x using Quot.ind; simp [dimap]
    simp [Fold.dimap, LawfulProfunctor.dimap_id]
  dimap_comp f f' g g' x := by
    cases x using Quot.ind; simp [dimap]
    simp [Fold.dimap, LawfulProfunctor.dimap_comp]

def foldl {F} [Foldable F] [LawfulFoldable F]
    (f : Fold α β) (ar : F α) : β :=
Quot.liftOn f (FoldImpl.foldl . ar) $ by
  intros x y H; cases H; simp [FoldImpl.foldl]
  next h₀ h₁ H =>
    apply H
    apply LawfulFoldable.foldl_sim <;> auto

def foldr {F} [Foldable F] [LawfulFoldable F]
    (f : Fold α β) (ar : F α) : β :=
Quot.liftOn f (FoldImpl.foldr . ar) $ by
  intros x y H; cases H; simp [FoldImpl.foldr]
  next h₀ h₁ H =>
    apply H
    apply LawfulFoldable.foldr_sim <;> auto

open Traversable LawfulTraversable

section scanl

variable {F} [Traversable F] [LawfulTraversable F]

section SIM
variable {σ σ'} (SIM : σ → σ' → Prop)
  -- (h₁ : ∀ (x : σ) (x' : σ') (y : α), SIM x x' → SIM (f x y) (g x' y))

def scanl_SIM :
    ApplicativeRel (StateM σ) (StateM σ') where
  R a b := ∀ x y, SIM x y →
      (a.run x).1 = (b.run y).1 ∧
      SIM (a.run x).2 (b.run y).2
  R_pure := by
    intros; simp [pure, StateT.pure, StateT.run]; auto
  R_seq := by
    intros _ _ _ _ _ _ h₀ h₁ x y Hxy; constructor
    focus
      simp
      cases (h₀ _ _ Hxy)
      -- cases (h₁ _ _ Hxy)
      apply congr
      . auto
      apply (h₁ _ _ _).1; auto
    focus
      simp
      apply (h₁ _ _ _).2
      apply (h₀ _ _ _).2; auto

def scanr_SIM :
    ApplicativeRel (Op1 (StateM σ)) (Op1 (StateM σ')) where
  R a b := ∀ x y, SIM x y →
      (a.run.run x).1 = (b.run.run y).1 ∧
      SIM (a.run.run x).2 (b.run.run y).2
  R_pure := by
    intros; simp [pure, StateT.pure, StateT.run]; auto
  R_seq := by
    intros _ _ _ _ _ _ h₀ h₁ x y Hxy; constructor
    focus
      simp
      apply congr
      . apply (h₀ _ _ _).1;
        apply (h₁ _ _ _).2; auto
      . apply (h₁ _ _ _).1; auto
    focus
      simp
      apply (h₀ _ _ _).2
      apply (h₁ _ _ _).2
      auto

end SIM

def scanl (f : Fold α β) (ar : F α) : F β :=
Quot.liftOn f (FoldImpl.scanl . ar) $ by
  intros a b h; cases h; next SIM h₀ h₁ h₂ =>
  next σ σ' x₀ y₀ f g out out' =>
  simp [FoldImpl.scanl, _root_.scanl, accuml, ← traverse_eq_mapM]
  let R := scanl_SIM SIM
  apply (traverse_sim (R := R) _ _ _ _ _ _ _).1
   <;> auto with 7

def accuml (f : Fold α β) (ar : F α) : F β × β :=
Quot.liftOn f (FoldImpl.accuml . ar) $ by
  intros a b h; cases h; next SIM h₀ h₁ h₂ =>
  next σ σ' x₀ y₀ f g out out' =>
  simp [FoldImpl.accuml, _root_.accuml, ← traverse_eq_mapM]
  let R := scanl_SIM SIM
  -- apply Prod.eta
  apply Prod.eta <;> simp
  . apply (traverse_sim (R := R) _ _ _ _ _ _ _).1
     <;> auto with 7
  . apply h₂
     <;> apply (traverse_sim (R := R) _ _ _ _ _ _ _).2
     <;> auto with 7

def accumr (f : Fold α β) (ar : F α) : F β × β :=
Quot.liftOn f (FoldImpl.accumr . ar) $ by
  intros a b h; cases h; next SIM h₀ h₁ h₂ =>
  next σ σ' x₀ y₀ f g out out' =>
  simp [FoldImpl.accumr, _root_.accumr, ← traverse_eq_mapM]
  let R := scanr_SIM SIM
  -- apply Prod.eta
  apply Prod.eta <;> simp
  . apply (traverse_sim (R := R) _ _ _ _ _ _ _).1
     <;> auto with 7
  . apply h₂
     <;> apply (traverse_sim (R := R) _ _ _ _ _ _ _).2
     <;> auto with 7

def scanr (f : Fold α β) (ar : F α) : F β :=
accumr f ar |>.1

end scanl

def mk (x₀ : α) (f : α → β → α) : Fold β α :=
Quot.mk _ $ FoldImpl.mk _ x₀ f id

def map (f : α → β) (x : Fold σ α) : Fold σ β :=
x.liftOn (Quot.mk _ ∘ Functor.map f) $ by
  intros x y H; cases H; simp [FoldImpl.foldl]
  apply Quot.sound; simp [(.<$>.)]
  next Heq h₀ H =>
  refine' ⟨_, Heq, _, _⟩
  . auto
  simp only [Function.comp]
  intros; apply congrArg; auto

theorem map_mk' {α β : Type u} (f : α → β) (x : FoldImpl σ α) :
  (map f <| Quot.mk _ x : Fold σ β) = Quot.mk _ (Functor.map f x) := by
apply Quot.sound; refl

instance : Functor (Fold α) where
  map := Fold.map

@[simp]
theorem map_mk {α β : Type u} (f : α → β) (x : FoldImpl σ α) :
  (Functor.map f <| Quot.mk _ x : Fold σ β) = Quot.mk _ (Functor.map f x) := by
apply Quot.sound; refl

def pure (x : α) : Fold σ α :=
Quot.mk _ (Pure.pure x)

theorem seq_lift {α β : Type u} (f f' : FoldImpl σ (α → β)) (x x' : FoldImpl σ α)
    (hf : FoldImpl.R f f')
    (hx : FoldImpl.R x x') :
  FoldImpl.R (Seq.seq f fun _ => x) (Seq.seq f' fun _ => x') := by
match f, f', hf with
| _, _, FoldImpl.R.intro Heq_f ha₀ ha₁ ha₂ .. =>
  match x, x', hx with
  | _, _, FoldImpl.R.intro Heq_x hb₀ hb₁ hb₂ .. =>
    let R | (x, y), (x', y') => Heq_f x x' ∧ Heq_x y y'
    refine' ⟨R, _, _, _⟩
    . auto
    focus
      intros x x' y; cases x; cases x'
      show  _ ∧ _ → _ ∧ _
      simp only ; intros h; auto
    focus
      intros x x' y; cases x; cases x'; cases y
      simp [Seq.seq]
      show _ = _
      rw [ha₂]; apply congrArg <;> auto
    focus
      auto

def seq {α β : Type u} (f : Fold σ (α → β)) (x : Unit → Fold σ α) : Fold σ β := by
apply Quot.liftOn₂ f (x ()) (λ a b => Quot.mk _ $ Seq.seq a (λ () => b))
 <;> intros <;> apply Quot.sound
 <;> apply seq_lift <;> auto


def seq_mk_mk' {α β : Type u} (f : FoldImpl σ (α → β)) (x : Unit → FoldImpl σ α) :
  (seq (Quot.mk _ f) (λ a => Quot.mk _ (x a)) : Fold σ β) =
  Quot.mk _ (Seq.seq f x) := by
apply Quot.sound; refl

instance : Applicative (Fold.{u} α) where
  pure := pure
  seq := seq

def seq_mk_mk {α β : Type u} (f : FoldImpl σ (α → β)) (x : Unit → FoldImpl σ α) :
  (Seq.seq (Quot.mk _ f) (λ a => Quot.mk _ (x a)) : Fold σ β) =
  Quot.mk _ (Seq.seq f x) := by
apply Quot.sound; refl

instance : LawfulFunctor (Fold α) where
  id_map {α} := by intros x; cases x using Quot.ind; refl
  comp_map {α β γ} f g := by intros x; cases x using Quot.ind; refl
  map_const := by intros; apply funext; intros; refl

inductive AssocSim : α × (β × γ) → (α × β) × γ → Prop
| intro {x y z} : AssocSim (x, (y, z)) ((x, y), z)

instance : LawfulApplicative (Fold α) where
  seq_assoc x f g:= by
    cases x using Quot.ind
    cases f using Quot.ind; cases g using Quot.ind;
    apply Quot.sound
    simp [Seq.seq]
    refine' ⟨AssocSim, _, _, _⟩ <;> simp
    . constructor
    all_goals intros; next h => cases h <;> simp
      <;> constructor
  seqLeft_eq x y := by
    cases x using Quot.ind; cases y using Quot.ind;
    simp [SeqLeft.seqLeft]
    simp [Seq.seq, (.<$>.), map_mk', seq_mk_mk']
  seqRight_eq x y := by
    cases x using Quot.ind; cases y using Quot.ind;
    simp [SeqRight.seqRight]
    simp [Seq.seq, (.<$>.), map_mk', seq_mk_mk']

  pure_seq x y := by
    cases y using Quot.ind -- with | mk y => cases y
    apply Quot.sound; simp
    refine' ⟨ λ (x,y) y' => y = y', _, _, _⟩
    . simp [Seq.seq, Pure.pure]
    focus
      intros x; cases x; simp
    focus
      intros; substAll; auto
    focus
      intros x; cases x; simp; intros; substAll; refl
  map_pure x y := by simp [Pure.pure, pure, (.<$>.), map, (. ∘ .)]

  seq_pure g x := by
    cases g using Quot.ind
    apply Quot.sound
    refine' ⟨ λ (y, _) y' => y = y', _, _, _⟩
    . simp [Seq.seq, Pure.pure]
    focus
      intros x; cases x; simp
    focus
      intros; substAll; refl
    focus
      intros x; cases x; simp; intros; substAll; refl

attribute [simp] seq_mk_mk

def dup (x : α) : α × α := (x, x)

inductive dup_sim : α → α × α → Prop
| intros {x} : dup_sim x (x, x)

theorem map_dup (x : Fold α β) : dup <$> x = (., .) <$> x <*> x := by
cases x using Quot.ind; simp
apply Quot.sound
refine' ⟨dup_sim, _, _, _⟩
focus simp; constructor
next a =>
  simp; intros _ _ _ h; cases h
  cases a; simp [Seq.seq]; constructor
next a =>
  simp; intros _ _ h; cases h
  cases a; simp [Seq.seq]; constructor

inductive hom_sim (h : β → γ) : β → γ → Prop
| intros x : hom_sim h x (h x)

def mk_hom (h : β → γ) (f : β → α → β) (g : γ → α → γ)
  (Hhom : ∀ x y, h (f x y) = g (h x) y) :
  h <$> mk x₀ f = mk (h x₀) g := by
simp [mk]; apply Quot.sound
refine' ⟨hom_sim h, _, _, _⟩
focus simp; constructor
focus
  intros _ _ _ h; cases h; rw [← Hhom]
  constructor
focus
  intros _ _ h; cases h; refl

def ofMonoid [Monoid m] (f : α → m) : Fold α m :=
Fold.mk 1 (λ x y => x * f y)

def ofMonoid_hom [Monoid m][Monoid m'] (h : MonoidHom m m') (f : α → m) :
  h.fn <$> ofMonoid f = ofMonoid (h.fn ∘ f) := by
simp [ofMonoid]
let g a b := a * h (f b)
rw [mk_hom (g := g), h.fn_id]
intros; apply h.fn_mul

def max [LT α] [DecidableRel LT.lt (α := α)] : Fold α (Option α) :=
Fold.mk none λ
  | none, y => some y
  | some x, y => some (_root_.max x y)

def min [LE α] [DecidableRel LE.le (α := α)] : Fold α (Option α) :=
Fold.mk none λ
  | none, y => some y
  | some x, y => some (_root_.min x y)

open One Zero

def toList : Fold α (List α) :=
List.reverse <$> Fold.mk [] (flip (.::.))

def count : Fold α Nat :=
Fold.mk 0 (λ n _ => n.succ)

def sum [Zero α] [Add α] : Fold α α :=
Fold.mk zero (.+.)

def prod [One α] [Mul α] : Fold α α :=
Fold.mk one (.*.)

end Fold
