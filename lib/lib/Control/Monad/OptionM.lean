
-- import Lib.Tactic

namespace Option

def traverse [Applicative m] (f : α → m β) : Option α → m (Option β)
| none => pure none
| some x => some <$> f x

attribute [simp] map_id
-- theorem map_id : Option.map (@id α) = id := rfl

theorem map_comp {f : α → β} {g : β → γ} :
  Option.map (g ∘ f) = Option.map g ∘ Option.map f :=
by funext x ; cases x <;> rfl

@[simp]
theorem map_some {f : α → β} : Option.map f (some x) = some (f x) := rfl

@[simp]
theorem map_none {f : α → β} : Option.map f none = none := rfl

end Option

namespace OptionT

theorem ext {x y : OptionT m α} : x.run = y.run → x = y := id

@[simp]
theorem run_mk {m : Type u → Type v} (x : m (Option α)) :
  OptionT.run (OptionT.mk x) = x := rfl

variable [Monad m] [LawfulMonad m]

@[simp]
theorem run_map (f : α → β) (x : OptionT m α) :
  (f <$> x).run = Option.map f <$> x.run := by
simp [(.<$>.), OptionT.bind, map_eq_pure_bind]
apply congrArg; funext a; cases a <;> rfl

@[simp]
theorem run_pure (x : α) :
  (pure x : OptionT m α).run = pure (some x) := rfl

@[simp]
theorem run_bind (f : α → OptionT m β) (x : OptionT m α) :
  (x.bind f).run = x.run >>= λ x =>
    match x with
    | none => pure none
    | some y => f y |>.run
:= by
simp [OptionT.bind]; apply congrArg; funext a
cases a <;> rfl

@[simp]
theorem run_bind' (f : α → OptionT m β) (x : OptionT m α) :
  (x >>= f).run = x.run >>= λ x =>
    match x with
    | none => pure none
    | some y => f y |>.run
:= run_bind f x

@[simp]
theorem run_seq (f : OptionT m (α → β)) (x : OptionT m α) :
  (f <*> x).run = f.run >>= λ a =>
    match a with
    | none => pure none
    | some a => Option.map a <$> x.run
:= by
simp [Seq.seq, map_eq_pure_bind]
simp; apply congrArg; funext a; cases a
case none => rfl
case some =>
  simp [map_eq_pure_bind]
  apply congrArg; funext a; cases a <;> rfl

instance : LawfulMonad (OptionT m) where
  map_const := by intros; funext a; rfl
  id_map x := by
    apply OptionT.ext; simp [Option.map_id]
  comp_map f g x := by
    apply OptionT.ext; simp [Option.map_comp, comp_map]
  pure_bind x f := OptionT.ext <| by simp
  seqLeft_eq x y := OptionT.ext <| by
    simp [SeqLeft.seqLeft, map_eq_pure_bind]
    apply congrArg; funext a; cases a <;> simp
    apply congrArg; funext a; cases a <;> simp <;> rfl
  seqRight_eq x y := OptionT.ext <| by
    simp [SeqRight.seqRight, map_eq_pure_bind]
    apply congrArg; funext a; cases a <;> simp [← map_eq_pure_bind]
  pure_seq g x := OptionT.ext <| by simp
  map_pure g x := OptionT.ext <| by simp
  seq_pure g x := OptionT.ext <| by
    simp [map_eq_pure_bind]
    apply congrArg; funext a; cases a <;> simp
  seq_assoc x g h := OptionT.ext <| by
    simp [map_eq_pure_bind]
    apply congrArg; funext a; cases a <;> simp
    apply congrArg; funext a; cases a <;> simp [Option.map_comp]
  bind_pure_comp f x := OptionT.ext <| by
    simp [map_eq_pure_bind]
    apply congrArg; funext a; cases a <;> simp
  bind_map f x := OptionT.ext <| by
    simp
    apply congrArg; funext a; cases a <;> simp
  bind_assoc x f g := OptionT.ext <| by
    simp
    apply congrArg; funext a; cases a <;> simp

end OptionT
