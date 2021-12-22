
import Sat.Lib.Array
import Sat.Lib.Foldable
import Sat.Lib.Equiv
import Sat.Tactics
import Sat.Quot

structure FoldImpl (α β : Type u) where
  γ : Type u
  x₀ : γ
  f : γ → α → γ
  out : γ → β

namespace FoldImpl

inductive R : FoldImpl α β → FoldImpl α β → Prop
| intro {γ γ' x₀ y₀ f g out out'} :
  (Heq : Equiv γ γ') →
  Heq.to x₀ = y₀ →
  (∀ x y, g (Heq.to x) y = Heq.to (f x y)) →
  (∀ x, out x = out' (Heq.to x)) →
  R ⟨γ, x₀, f, out⟩ ⟨γ', y₀, g, out'⟩

namespace R

variable {x y z : FoldImpl α β}

theorem refl : R x x := by
cases x
refine' ⟨Equiv.id, _, _, _⟩
<;> intros
<;> simp

instance : Reflexive (@R α β) := ⟨ @refl _ _ ⟩

local infixr:60 " ⊚ " => Equiv.comp

theorem trans (Hxy : R x y) (Hyz : R y z) : R x z := by
cases Hxy with | intro Heq a b =>
cases Hyz with | intro Heq' a' b' =>
refine' ⟨(Heq' ⊚ Heq), _, _, _⟩
<;> intros
<;> simp [*]

theorem symm (Hxy : R x y) : R y x := by
cases Hxy with | intro Heq a b c =>
-- have a := Eq.symm a
refine' ⟨Heq.symm, _, _, _⟩
<;> intros
<;> simp [*]
. rw [← a]; simp
. simp [Equiv.eq_inv_iff, ← b]

end R

-- def run : (f : FoldImpl α β) → (ar : Array α) → β
-- | ⟨γ, x₀, f, out⟩, ar => out <| ar.foldl f x₀


def run {F} [Foldable F] : (f : FoldImpl α β) → (ar : F α) → β
| ⟨γ, x₀, f, out⟩, ar => out <| Foldable.foldl f x₀ ar

instance : Functor (FoldImpl α) where
  map f x := { x with out := f ∘ x.out }

instance : Applicative (FoldImpl.{u} α) where
  pure x := ⟨ PUnit, ⟨ ⟩, λ x _ => x, λ _ => x ⟩
  seq {β γ} f x :=
      let x := x ();
         { γ := f.γ × x.γ,
           x₀ := (f.x₀, x.x₀),
           f := λ ⟨a,b⟩ z => ⟨f.f a z, x.f b z⟩,
           out := λ ⟨a, b⟩ => f.out a <| x.out b
          }

end FoldImpl

def Fold (α β : Type _) := Quot (@FoldImpl.R α β)

namespace Fold

def run {F} [Foldable F] [LawfulFoldable F]
    (f : Fold α β) (ar : F α) : β :=
Quot.liftOn f (FoldImpl.run . ar) $ by
  intros x y H; cases H; simp [FoldImpl.run]
  next h₀ H =>
    rw [H]; apply congrArg
    apply LawfulFoldable.foldl_hom
    . auto
    . intros; rw [h₀]

-- def run (f : Fold α β) (ar : Array α) : β :=
-- Quot.liftOn f (FoldImpl.run . ar) $ by
--   intros x y H; cases H; simp [FoldImpl.run]
--   next h₀ H =>
--     rw [H]; apply congrArg
--     apply Array.foldl_hom
--     . intros; rw [h₀]
--     . auto

def map (f : α → β) (x : Fold σ α) : Fold σ β :=
x.liftOn (Quot.mk _ ∘ Functor.map f) $ by
  intros x y H; cases H; simp [FoldImpl.run]
  apply Quot.sound; simp [(.<$>.)]
  next Heq h₀ H =>
  refine' ⟨_, Heq, h₀, _⟩
  intros; simp [Function.comp, H]

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
| _, _, FoldImpl.R.intro Heq_f .. =>
  match x, x', hx with
  | _, _, FoldImpl.R.intro Heq_x .. =>
    refine' ⟨Equiv.prodCongr Heq_f Heq_x, _, _, _ ⟩
    <;> intros <;> simp [Seq.seq, *]

def seq {α β : Type u} (f : Fold σ (α → β)) (x : Unit → Fold σ α) : Fold σ β := by
apply Quot.liftOn₂ f (x ()) (λ a b => Quot.mk _ $ Seq.seq a (λ () => b))
<;> intros <;> apply Quot.sound <;> apply seq_lift <;> auto

def seq_mk_mk' {α β : Type u} (f : FoldImpl σ (α → β)) (x : Unit → FoldImpl σ α) :
  (seq (Quot.mk _ f) (λ a => Quot.mk _ (x a)) : Fold σ β) =
  Quot.mk _ (Seq.seq f x) := by
apply Quot.sound; refl

instance : Applicative (Fold.{u} α) where
  pure := pure
  seq := seq

-- @[simp]
def seq_mk_mk {α β : Type u} (f : FoldImpl σ (α → β)) (x : Unit → FoldImpl σ α) :
  (Seq.seq (Quot.mk _ f) (λ a => Quot.mk _ (x a)) : Fold σ β) =
  Quot.mk _ (Seq.seq f x) := by
apply Quot.sound; refl

instance : LawfulFunctor (Fold α) where
  id_map {α} := by intros x; cases x using Quot.ind; refl
  comp_map {α β γ} f g := by intros x; cases x using Quot.ind; refl
  map_const := by intros; apply funext; intros; refl

instance : LawfulApplicative (Fold α) where
  seq_assoc x f g:= by
    cases x using Quot.ind
    cases f using Quot.ind; cases g using Quot.ind;
    apply Quot.sound
    refine' ⟨Equiv.assoc.symm, _, _, _⟩
    <;> intros <;> simp [Seq.seq]
    <;> simp [Seq.seq, (.<$>.), map_mk', seq_mk_mk']
  seqLeft_eq x y := by
    cases x using Quot.ind; cases y using Quot.ind;
    simp [SeqLeft.seqLeft]
    simp [Seq.seq, (.<$>.), map_mk', seq_mk_mk']
  seqRight_eq x y := by
    cases x using Quot.ind; cases y using Quot.ind;
    simp [SeqRight.seqRight]
    simp [Seq.seq, (.<$>.), map_mk', seq_mk_mk']

  pure_seq x y := by
    cases y using Quot.ind;
    simp [Seq.seq, Pure.pure, pure, (.<$>.), map_mk', seq_mk_mk']
    apply Quot.sound
    refine' ⟨Equiv.left_unitor, _, _, _⟩
    <;> intros <;> simp [Seq.seq]

  map_pure x y := by
    simp [Seq.seq, Pure.pure, pure, (.<$>.), map_mk', seq_mk_mk']; refl

  seq_pure g x := by
    cases g using Quot.ind;
    simp [Seq.seq, Pure.pure, pure, (.<$>.), map_mk', seq_mk_mk']
    apply Quot.sound
    refine' ⟨Equiv.right_unitor, _, _, _⟩
    <;> intros <;> simp [Seq.seq]


end Fold
