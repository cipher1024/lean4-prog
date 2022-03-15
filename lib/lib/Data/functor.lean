
import Lib.Algebra.Monoid
import Lib.Attributes
import Lib.Function
import Lib.Tactic

namespace Functor
variable {F} [Functor F] [LawfulFunctor F]
attribute [functor] LawfulFunctor.id_map

@[simp, functor]
theorem map_id :
  map (f := F) (@id α) = id := by
ext; simp

@[simp, functor]
theorem map_comp (f : α → β) (g : β → γ) :
  map g (map f x) = map (f := F) (g ∘ f) x := by
rw [comp_map]

@[simp, functor]
theorem map_comp' (f : α → β) (g : β → γ) :
  map g ∘ map f = map (f := F) (g ∘ f) := by
ext; simp only [(.∘.),map_comp]

end Functor

namespace Applicative

variable {α β}
variable {F : Type u → Type v} [Applicative F] [LawfulApplicative F]

attribute [functor] seq_assoc pure_seq seq_pure

-- @[functor]
theorem pure_seq' (f : α → β) (x : F α) :
  f <$> x = pure f <*> x :=
by simp [pure_seq]

@[simp, functor]
theorem seq_map {α β γ : Type u}
        {f : α → β} {x : F (β → γ)} {y : F α} :
  x <*> (f <$> y) = (.∘f) <$> x <*> y := by
simp only [pure_seq']
rw [seq_assoc]
simp only [seq_pure, pure_seq, Functor.map_comp]
refl

@[simp, functor]
theorem map_seq {α β γ : Type u}
        {f : β → γ} {x : F (α → β)} {y : F α} :
  f <$> (x <*> y) = (f∘.) <$> x <*> y := by
simp only [pure_seq']
simp only [pure_seq, map_pure, seq_assoc]

end Applicative

def Id.mk (x : α) : Id α := x
def Comp (F : Type v → Type w) (G : Type u → Type v) (α : Type u) := F (G α)

namespace Comp
variable
  {F : Type v → Type w} {G : Type u → Type v} {α : Type u}

def mk (x : F (G α)) : Comp F G α := x
def run (x : Comp F G α) : F (G α) := x

instance [Functor F] [Functor G] : Functor (Comp F G) where
  map f := Functor.map (f := F) (Functor.map (f := G) f)

instance [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] : LawfulFunctor (Comp F G) where
  id_map := by intros; simp [id_map, Functor.map]
  comp_map := by intros; simp [id_map, Functor.map]
  map_const := by intros; simp [id_map, Functor.map]; apply funext; intro; refl

instance [Applicative F] [Applicative G] : Applicative (Comp F G) where
  pure x := Pure.pure (f := F) $ Pure.pure (f := G) x
  seq {α β} (f : F (G (α → β))) (x : Unit → F (G α)) :=
    show F (G β) from
    Seq.seq ((.<*>.) <$> f) x

theorem comp_seq_def [Applicative F] [Applicative G]
        {α β : Type u}
        (x : Comp F G (α → β)) (y : Comp F G α) :
  x <*> y = ((.<*>.) <$> x <*> y : F (G β)) := rfl

open Applicative

instance [Applicative F] [LawfulApplicative F] [Applicative G] [LawfulApplicative G] :
         LawfulApplicative (Comp F G) where
  seqLeft_eq := by intros; refl
  seqRight_eq := by intros; refl
  pure_seq := by intros; simp [pure_seq, pure, Seq.seq, (.<$>.)]
  map_pure := by intros; simp [pure_seq, pure, Seq.seq, (.<$>.)]
  seq_pure := by intros; simp [pure_seq, pure, Seq.seq, (.<$>.), (.∘.)]
  seq_assoc := by
    intros; simp [pure_seq, pure, comp_seq_def, (.<$>.), (.∘.), seq_assoc]

end Comp

def Const (ω : Type u) (α : Type v) := ω
def Const.mk {ω : Type u} {α : Type v} (w : ω) : Const ω α := w
def Const.run {ω : Type u} {α : Type v} (w : Const ω α) : ω := w

namespace Const

instance : Functor (Const ω) where
  map f x := x

instance : LawfulFunctor (Const ω) where
  id_map := by intros; refl
  map_const := by intros; refl
  comp_map := by intros; refl

open One

instance [One ω] : Pure (Const ω) where
  pure _ := (1 : ω)

instance [Mul ω] : Seq (Const ω) where
  seq (x : ω) (y : Unit → ω) := (x * y () : ω)

instance [One ω] [Mul ω] : Applicative (Const ω) where
  pure := pure
  seq := Seq.seq

instance [Monoid ω] : LawfulApplicative (Const ω) := by
constructor <;> intros
<;> simp [(.<$>.), Seq.seq, pure, SeqLeft.seqLeft, SeqRight.seqRight]

end Const

section defs

variable (F G : Type u → Type _) [Applicative F] [Applicative G]

structure ApplicativeRel where
  R {α} : F α → G α → Prop
  R_pure {α} {x : α} : R (pure x) (pure x)
  R_seq {α β : Type u} (f : F (α → β)) (x : F α) (f' : G (α → β)) (x' : G α) :
    R f f' →
    R x x' →
    R (f <*> x) (f' <*> x')

structure ApplicativeHom where
  fn {α} : F α → G α
  fn_pure {α} {x : α} : fn (pure x) = pure x
  fn_seq {α β : Type u} (f : F (α → β)) (x : F α) :
    fn (f <*> x) = fn f <*> fn x

end defs

attribute [simp] ApplicativeHom.fn_pure ApplicativeHom.fn_seq

namespace ApplicativeRel

variable {F G : Type u → Type _} [Applicative F] [Applicative G]

instance : CoeFun (ApplicativeRel F G) (λ _ => {α : Type _} → F α → G α → Prop) where
  coe x := x.R

variable [LawfulApplicative F] [LawfulApplicative G]
variable (R : ApplicativeRel F G)

attribute [auto] ApplicativeRel.R_pure ApplicativeRel.R_seq

@[auto]
theorem naturality {α β} (g : α → β) (x : F α) (x' : G α)
        (hR : R x x') :
  R (g <$> x) (g <$> x') :=
by simp [← pure_seq]; auto

-- def toApplicativeHom : ApplicativeHom F G where
--   fn x := f x = y
--   fn_pure := by intros; simp
--   fn_seq := by intros; simp [*]

end ApplicativeRel

namespace Functor

variable {F} [Functor F] [LawfulFunctor F]
variable {f : α → β}

section LeftInv

variable {g : β → α} (Hfg : LeftInv f g)

theorem LeftInv_map : LeftInv (map (f:=F) f) (map g) := by
simp [LeftInv, Hfg]

end LeftInv

section HasLeftInv

variable (Hf : HasLeftInv f)

theorem HasLeftInv_map : HasLeftInv (map (f:=F) f) := by
obtain ⟨g, Hg⟩ from Hf
exists map (f := F) g
simp [LeftInv, Hg]

end HasLeftInv

section HasRightInv

variable (Hf : HasRightInv f)

theorem HasRightInv_map : HasRightInv (map (f:=F) f) := by
obtain ⟨g, Hg⟩ from Hf
exists map (f := F) g
simp [RightInv, Hg]

end HasRightInv

section HasRightInv

variable (Hf : HasLeftInv f)

theorem Injective_map : Injective (map (f:=F) f) := by
auto [Injective_of_HasLeftInv,HasLeftInv_map]

end HasRightInv

end Functor

namespace ApplicativeHom

variable {F G : Type u → Type _} [Applicative F] [Applicative G]

instance : CoeFun (ApplicativeHom F G) (λ _ => {α : Type _} → F α → G α) where
  coe x := x.fn

variable [LawfulApplicative F] [LawfulApplicative G]
variable (f : ApplicativeHom F G)

@[simp]
theorem naturality {α β} (g : α → β) (x : F α) :
    f (g <$> x) = g <$> f x := by
simp [← pure_seq, fn_seq, fn_pure]

def toApplicativeRel : ApplicativeRel F G where
  R x y := f x = y
  R_pure := by intros; simp
  R_seq := by intros; simp [*]

end ApplicativeHom

def Op1 (F : Type u → Type v) α := F α
def Op1.mk {F : Type u → Type v} {α} (x : F α) : Op1 F α := x
def Op1.run {F : Type u → Type v} {α} (x : Op1 F α) : F α := x

namespace Op1

instance {F} [Functor F] : Functor (Op1 F) where
  map := @Functor.map F _

instance {F} [Functor F] [H : LawfulFunctor F] : LawfulFunctor (Op1 F) := by
constructor <;> intros
. simp [Functor.mapConst, Function.const]; ext; refl
. simp [(.<$>.)]
. simp [(.<$>.)]


variable {F} [Applicative F]
-- set_option pp.explicit true

instance : Applicative (Op1 F) where
  pure := pure (f := F)
  seq f x := ((λ x f => f x) <$> x () <*> f : F _)
  map := Functor.map (f := F)
-- #print instApplicativeOp1
variable [LawfulApplicative F]

@[simp]
theorem map_eq {α β : Type u} {f : α → β} (x : Op1 F α) :
  (Op1.run $ f <$> x) = (f <$> Op1.run x) := rfl

@[simp]
theorem pure_eq {α : Type u} (x : α) :
  (@Op1.run F _ $ pure x) = (pure x) := rfl

@[simp]
theorem seq_eq {α β : Type u} (f : Op1 F (α → β))
        (x : Unit → Op1 F α) :
  Op1.run (Seq.seq f x) =
  ((λ x f => f x) <$> Op1.run (x ()) <*> Op1.run f) := rfl

@[simp]
protected theorem seqLeft_eq {α β : Type u} (f : Op1 F β)
        (x : Unit → Op1 F α) :
  Op1.run (SeqLeft.seqLeft f x) =
  SeqRight.seqRight (run $ x ()) (λ _ => run f)  := by
change SeqLeft.seqLeft f x
  with Seq.seq (Function.const _ <$> f) x
simp only [seq_eq, map_eq, (.∘.), Function.const,
           seqRight_eq, Applicative.seq_map, Functor.map_comp]
refl

@[simp]
protected theorem seqRight_eq {α β : Type u} (f : Op1 F β)
        (x : Unit → Op1 F α) :
  Op1.run (SeqRight.seqRight f x) =
  SeqLeft.seqLeft (run $ x ()) (λ _ => run f)  := by
change SeqRight.seqRight f x
  with Seq.seq (Function.const _ id <$> f) x
simp only [seq_eq, map_eq, (.∘.), Function.const,
           seqLeft_eq, Applicative.seq_map, Functor.map_comp]
refl

theorem ext (x y : Op1 F α) : x.run = y.run → x = y := id

instance : LawfulApplicative (Op1 F) := by
constructor <;> intros <;> apply Op1.ext
<;> simp [seqLeft_eq, seqRight_eq, pure_seq, seq_assoc]
<;> refl

end Op1

namespace Const

@[simp]
theorem run_pure {α ω} [Monoid ω] x :
  @Const.run ω α (pure x) = 1 := rfl

@[simp]
theorem run_seq {α β : Type _} {ω} [Monoid ω]
        (x : Const ω (α → β)) (y : Unit → Const ω α) :
  Const.run (Seq.seq x y) = Const.run x * Const.run (y ()) := rfl

@[simp]
theorem run_mk {α ω} x :
  @Const.run ω α (Const.mk x) = x := rfl

@[simp]
theorem map_mk {α β ω} (f : α → β) x :
  f <$> @Const.mk ω α x = Const.mk x := rfl

@[simp]
theorem run_map {α β ω} (f : α → β) x :
  @Const.run ω β (f <$> x) = Const.run x := rfl

end Const

namespace Comp
open Functor
@[simp]
theorem run_mk {F G : Type _ → Type _} (x : F (G α)) :
  Comp.run (Comp.mk x) = x := rfl

@[simp]
theorem run_pure {F G} [Applicative F] [Applicative G] (x : α) :
  Comp.run (pure x : Comp F G α) = pure (pure x) := rfl

@[simp]
theorem run_seq {α β : Type _} {F G} [Applicative F] [Applicative G]
        (x : Comp F G (α → β)) y :
  Comp.run (Seq.seq x y) =
  Seq.seq ((.<*>.) <$> Comp.run x) (Comp.run ∘ y) := rfl

@[simp]
theorem run_map {α β : Type _} {F G} [Functor F] [Functor G]
        (f : α → β) (x : Comp F G α) :
  Comp.run (f <$> x) =
  Functor.map f <$> (Comp.run x) := rfl

@[simp]
theorem map_mk {α β : Type _} {F G} [Functor F] [Functor G]
        (f : α → β) (x : F (G α)) :
  f <$> Comp.mk x =
  Comp.mk (map f <$> x) := rfl

end Comp
