
import Sat.Lib.Attributes
import Sat.Lib.Monoid
import Sat.Tactics

namespace Functor
variable {F} [Functor F] [LawfulFunctor F]
attribute [functor] LawfulFunctor.id_map

@[simp, functor]
theorem map_id :
  map (f := F) (@id α) = id := by
ext; simp

@[simp, functor]
theorem map_comp' (f : α → β) (g : β → γ) :
  map g ∘ map f = map (f := F) (g ∘ f) := by
ext; simp [comp_map]

@[simp, functor]
theorem map_comp (f : α → β) (g : β → γ) :
  map g (map f x) = map (f := F) (g ∘ f) x := by
simp [comp_map]

end Functor

namespace Applicative

variable {α β}
variable {F} [Applicative F] [LawfulApplicative F]

attribute [functor] seq_assoc pure_seq seq_pure

-- @[functor]
theorem pure_seq' (f : α → β) (x : F α) :
  f <$> x = pure f <*> x :=
by simp [pure_seq]

@[simp, functor]
theorem seq_map {α β γ : Type _}
        {f : α → β} {x : F (β → γ)} {y : F α} :
  x <*> (f <$> y) = (.∘f) <$> x <*> y := by
simp only [pure_seq']
rw [seq_assoc]
simp only [seq_pure, pure_seq, Functor.map_comp]
refl

@[simp, functor]
theorem map_seq {α β γ : Type _}
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
    apply congr _ rfl
    apply congrArg
    simp [pure_seq, pure, comp_seq_def, (.<$>.), (.∘.), seq_assoc]
    rw [pure_seq', pure_seq', seq_assoc]
    apply congrFun; apply congrArg
    simp [seq_assoc]
    apply congrFun; apply congrArg
    apply congrArg; refl

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
  pure _ := one (α := ω)

instance [Mul ω] : Seq (Const ω) where
  seq (x : ω) (y : Unit → ω) := (x * y () : ω)

instance [One ω] [Mul ω] : Applicative (Const ω) where
  pure := pure
  seq := Seq.seq

instance [Monoid ω] : LawfulApplicative (Const ω) := by
constructor <;> intros
<;> simp [(.<$>.), Seq.seq, pure, SeqLeft.seqLeft, SeqRight.seqRight]

end Const

structure ApplicativeHom (F G : Type u → Type _) [Applicative F] [Applicative G] where
  fn {α} : F α → G α
  fn_pure {α} {x : α} : fn (pure x) = pure x
  fn_seq {α β : Type u} (f : F (α → β)) (x : F α) :
    fn (f <*> x) = fn f <*> fn x

attribute [simp] ApplicativeHom.fn_pure ApplicativeHom.fn_seq

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

instance : Applicative (Op1 F) where
  pure := pure (f := F)
  seq f x := ((λ x f => f x) <$> x () <*> f : F _)
  map := Functor.map (f := F)

variable [LawfulApplicative F]

-- set_option pp.explicit true

theorem map_eq {α β : Type u} {f : α → β} (x : Op1 F α) :
  (f <$> x : Op1 F β) = (f <$> x : F β) := rfl

theorem pure_eq {α : Type u} (x : α) :
  (pure x : Op1 F α) = (pure x : F α) := rfl

theorem seq_eq {α β : Type u} (f : Op1 F (α → β)) (x : Op1 F α) :
  (f <*> x : Op1 F β) = ((λ x f => f x) <$> x <*> f : F β) := rfl

instance : LawfulApplicative (Op1 F) := by
-- have : LawfulFunctor (Op1 F) := inferInstanceAs (LawfulFunctor F)
constructor <;> intros
<;> simp [Function.const, seq_eq, flip, ← seqLeft_eq, ← seqRight_eq,
          seq_pure, pure_seq, pure_eq, map_pure, map_eq, (.∘.)]
<;> try refl
<;> simp [pure_eq, map_pure, pure_seq, seq_eq, seq_assoc, seqLeft_eq, seqRight_eq]
admit
admit
rw [Applicative.map_seq, seq_assoc]
simp only [← comp_map, (.∘.)]
rw [Applicative.seq_map]
apply congrFun; apply congrArg
simp only [← comp_map, (.∘.)]

end Op1
