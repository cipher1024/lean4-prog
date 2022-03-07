import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Match
import Lean.Meta.Tactic.Split
import Lean.PrettyPrinter
import Lib.Data.List.Control
import Lib.Data.Array.Control

class Reflexive (R : α → α → Prop) where
  refl x : R x x

class Symmetric (R : α → α → Prop) where
  symmetry {x y} : R x y → R y x

instance : @Reflexive α (.=.) where
  refl _ := rfl

instance : Reflexive (.↔.) where
  refl _ := Iff.rfl

instance : @Symmetric α (.=.) where
  symmetry := Eq.symm

instance : Symmetric (.↔.) where
  symmetry := Iff.symm

instance : Reflexive (.→.) where
  refl _ := id

instance : @Reflexive Nat LE.le where
  refl := Nat.le_refl

macro "rintro1 " t:term : tactic =>
  `(tactic| intro x; match x with | $t:term => ?_)

syntax "rintro " term,* : tactic

macro_rules
| `(tactic| rintro ) => `(tactic| skip)
| `(tactic| rintro $t, $ts) =>
  `(tactic| rintro1 $t <;> rintro $ts )

macro "obtain " p:term " from " d:term : tactic =>
  `(tactic| match $d:term with | $p:term => ?_)

macro "obtain " p:term " : " q:term " from " d:term : tactic =>
  `(tactic|
    have h : $q := $d;
    match h with | $p:term => ?_)

namespace Lean.Elab.Tactic
open Lean.Meta

elab "obtain" "!" p:term " from " d:term : tactic =>
  withMainContext do
    let (e, mvarIds') ← elabTermWithHoles d none `specialize (allowNaturalHoles := true)
    let h := e.getAppFn
    if h.isFVar then
      let localDecl ← getLocalDecl h.fvarId!
      let mvarId ← assert (← getMainGoal) localDecl.userName (← inferType e).headBeta e
      let (newHyp', mvarId) ← intro1P mvarId
      let mvarId ← tryClear mvarId h.fvarId!
      replaceMainGoal (mvarId :: mvarIds')
      withMainContext do
        let newHyp ← mkIdentFromRef
            <| (← getLCtx).get! newHyp' |>.userName
        let myMatch ←
          `(tactic| match $newHyp:term with | $p => ?_ )
        let stx ← getRef
        withMacroExpansion stx myMatch
          <| Lean.Elab.Tactic.evalMatch myMatch
        liftMetaTactic1 <| (tryClear . newHyp')
    else
      throwError "'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"

macro "obtain!" p:term " from " d:term : tactic =>
  `(tactic| obtain ! $p from $d)

end Lean.Elab.Tactic

macro "left" : tactic =>
  `(tactic| apply Or.inl)

macro "right" : tactic =>
  `(tactic| apply Or.inr)

syntax "refl" : tactic

macro "congr" : tactic =>
  `(tactic| repeat first | apply congrArg | apply congrFun | refl)

-- TODO: import mathlib and get rid of this
syntax "extOrSkip" (ident)* : tactic
syntax "ext" (ident)* : tactic

macro_rules
| `(tactic| extOrSkip) => `(tactic| skip)
| `(tactic| extOrSkip $x $xs) =>
  `(tactic| apply funext; intro $x; extOrSkip $xs)

macro_rules
| `(tactic| ext) => `(tactic| repeat (apply funext; intro))
| `(tactic| ext $xs) =>
  `(tactic| extOrSkip $xs)

syntax "change" term "with" term : tactic


macro "change" t:term "with" t':term : tactic =>
  `(tactic| have H : $t = $t' := rfl; rw [H]; clear H )

namespace Lean.Elab.Tactic

initialize registerTraceClass `refl
initialize registerTraceClass `substAll

open Expr Lean.Meta

def applyUnifyAll (g : MVarId) (lmm : Expr) (allowMVars := false) : MetaM (List MVarId) := do
  trace[auto.lemmas]"try {lmm}"
  trace[auto.lemmas]"type: {(← inferType lmm)}"
  trace[auto.goal]"goal {(← inferType (mkMVar g))}"
  let gs ← try apply g lmm
           catch e =>
             trace[auto.apply.failure]"error: {lmm}"
             trace[auto.apply.failure]"error: {e.toMessageData}"
             throw e
  trace[auto.lemmas]"{gs.length} new goals"
  let ls ← gs.mapM λ v => inferType (mkMVar v)
  trace[auto.lemmas]"{ls} all new goals"
  let b ← gs.allM λ v => do
    return (← inferType (← inferType (mkMVar v))).isProp
  if ¬ (allowMVars ∨ b) then
    trace[auto.lemmas]"failed"
    failure
  trace[auto.lemmas]"success"
  return gs

def tacRefl : TacticM Unit := do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  match g with
  | (app (app R x _) y _) => liftMetaTactic λ g => do
    let cl ← mkAppOptM ``Reflexive #[none, R]
    let inst ← synthInstance cl
    let reflLmm ← mkAppOptM ``Reflexive.refl #[none, R, inst]
    apply g reflLmm
  | _ =>
    trace[refl]"ctorName: {g.ctorName}"
    let reflLmm ← mkConstWithFreshMVarLevels ``Reflexive.refl
    liftMetaTactic (apply . reflLmm) <|>
      throwError "Expection a reflexive relation: R x y"

def tacSymm : TacticM Unit := do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  match g with
  | (app (app R x _) y _) => liftMetaTactic λ g => do
    let cl ← mkAppOptM ``Symmetric #[none, R]
    let inst ← synthInstance cl
    let symmLmm ← mkAppOptM ``Symmetric.symmetry #[none, R, inst]
    apply g symmLmm
  | _ =>
    trace[refl]"ctorName: {g.ctorName}"
    let symmLmm ← mkConstWithFreshMVarLevels ``Symmetric.symmetry
    liftMetaTactic (apply . symmLmm) <|>
      throwError "Expection a symmetric relation: R x y"

def tacSubstAll : TacticM Unit := do
  let lctx ← getLCtx
  trace[substAll] "hyps: {lctx.getFVars}"

  for h in lctx do
    let t := (← instantiateMVars h.type).consumeMData

    if ¬ h.isAuxDecl then
      match t with
      | app (app eq lhs _) rhs _ =>
        let lc ← getLCtx
        trace[substAll] "{h.userName} : {t}"
        if let Option.some _ := lc.find? h.fvarId then
          trace[substAll] "valid hyp"
          if eq.isAppOf `Eq ∧ (lhs.isFVar ∨ rhs.isFVar) then
            trace[substAll] "var eq"
            liftMetaTactic1 (subst .  h.fvarId)
      | _ =>
        trace[substAll] "ignore {h.userName} :  {t.ctorName} {t}"

def SearchT (δ : Type u) (m : Type u → Type v) (α : Type u) := (α → m δ) → m δ

namespace SearchT

variable {σ : Type} {m : Type → Type}
variable {α β : Type}

def pure (x : α) : SearchT δ m α :=
λ f => f x

def bind (x : SearchT δ m α) (f : α → SearchT δ m β) : SearchT δ m β :=
λ g => x λ a => f a g

instance : Monad (SearchT δ m) where
  pure := pure
  bind := bind

section Alternative
variable [Alternative m] [Monad m] [MonadBacktrack σ m]

def failure  : SearchT δ m α :=
λ f => Alternative.failure

def orElse (x : SearchT δ m α) (y : Unit → SearchT δ m α) : SearchT δ m α :=
λ f => do
  let s ← saveState
  Alternative.orElse (x f) λ _ => restoreState s >>= λ _ => y () f

instance : Alternative (SearchT δ m) where
  failure := failure
  orElse := orElse

end Alternative

def pick [Alternative m] [Monad m] [MonadBacktrack σ m] (l : List α) : SearchT δ m α :=
λ g => do
  let s ← saveState
  l.firstM λ a => do
    restoreState s
    g a

def pick' [Alternative m] [Monad m] [MonadBacktrack σ m] (l : Array α) : SearchT δ m α :=
λ g => do
  let s ← saveState
  l.firstM λ a => do
    restoreState s
    g a

instance [Bind m] : MonadLift m (SearchT δ m) where
  monadLift x f := x >>= f

instance [Bind m] [MonadEnv m] : MonadEnv (SearchT δ m) where
  getEnv f := getEnv >>= f
  modifyEnv x f := modifyEnv x >>= f

-- instance [Bind m] [MonadExceptOf ε m] : MonadExceptOf ε (SearchT δ m) where
--   throw e f := throw e
--   tryCatch x f g := _

instance [Monad m] [MonadRef m] : MonadRef (SearchT δ m) where
  getRef f := getRef >>= f
  withRef s x f := withRef s (x f)

instance [Bind m] [AddErrorMessageContext m] : AddErrorMessageContext (SearchT δ m) where
  add s m f := AddErrorMessageContext.add s m >>= f

def run [Pure m] (x : SearchT α m α) : m α := x Pure.pure

end SearchT

abbrev SearchTacticM δ := SearchT δ TacticM

namespace SearchTacticM

-- instance [Bind m] : MonadFunctor m (SearchT m) where
--   monadMap f x δ g := f _

def focus {α : Type} (x : SearchTacticM δ α) : SearchTacticM δ α := do
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  setGoals [mvarId]
  let a ← x
  let mvarIds' ← getUnsolvedGoals
  setGoals (mvarIds' ++ mvarIds)
  pure a

def focusAndDone {α} (tactic : SearchTacticM δ α) : SearchTacticM δ α :=
  focus do
    let a ← tactic
    done
    pure a

end SearchTacticM

def isDone : TacticM Bool :=
Option.isSome <$> optional done

def allGoals [Monad m] [MonadLift TacticM m] (tac : m PUnit) : m PUnit := do
let gs ← getGoals
let gs' ← gs.mapM λ g => do setGoals [g]; tac; getGoals
setGoals gs'.join

def tryTac [Alternative m] [Pure m] (x: m Unit) : m Unit :=
Alternative.orElse x (λ _ => pure ())

def iterate [Monad m] [MonadLift TacticM m]: Nat → m PUnit → m PUnit
| 0, _ => pure ()
| Nat.succ n, tac => do
  unless (← isDone) do
    -- tryTac (do
      ( traceM `auto.iterate <| return s!"iterate n = {n}" : TacticM Unit)
      tac
      allGoals $ iterate n tac

def tacMyApply (e : Expr) : TacticM Unit :=
  liftMetaTactic (applyUnifyAll . e)

end Lean.Elab.Tactic

open Lean.Elab.Tactic

elab "apply1" t:term : tactic =>
  withMainContext (do tacMyApply (← elabTerm t none))
elab "refl" : tactic => withMainContext Lean.Elab.Tactic.tacRefl
elab "symmetry" : tactic => withMainContext Lean.Elab.Tactic.tacSymm
elab "substAll" : tactic => withMainContext Lean.Elab.Tactic.tacSubstAll

macro "exfalso" : tactic =>
  `(tactic| apply False.elim)

macro "byContradiction" h: ident : tactic =>
  `(tactic| apply Classical.byContradiction; intro h)

syntax "trans" (term)? : tactic

macro_rules
| `(tactic| trans ) => `(tactic| trans ?middle)
| `(tactic| trans $t:term) =>
  `(tactic|
    -- show (?rel : ?α → ?α → ?t) ?x ?y ;
    focus
      refine' Trans.trans (r := ?rel) (s := ?rel) (t := ?rel)
                         (self := ?inst) (b := $t) ?first ?second;
      case inst => infer_instance
      rotate_right 2 )

instance : @Trans Nat Nat Nat LE.le LE.le LE.le where
  trans := Nat.le_trans

instance : @Trans Nat Nat Nat LT.lt LT.lt LT.lt where
  trans := Nat.lt_trans

instance : @Trans Nat Nat Nat GE.ge GE.ge GE.ge where
  trans h h' := Nat.le_trans h' h

instance : @Trans Nat Nat Nat GT.gt GT.gt GT.gt where
  trans h h' := Nat.lt_trans h' h

open Lean.Elab.Tactic
open Lean

syntax (name := auto) "auto" : attr
syntax (name := eauto) "eauto" : attr

abbrev AutoExtension := SimpleScopedEnvExtension Name NameSet

def mkAutoAttr (attrName : Name) (attrDescr : String) (ext : AutoExtension) : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    add   := fun declName stx attrKind =>
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        match info with
        | ConstantInfo.inductInfo i =>
          for c in i.ctors do
            ext.add c attrKind
        | _ =>
          ext.add declName attrKind
      discard <| go.run {} {}
    erase := fun declName => do
      let s := ext.getState (← getEnv)
      let s := s.erase declName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }

def mkAutoExt (extName : Name) : IO AutoExtension :=
  registerSimpleScopedEnvExtension {
    name     := extName
    initial  := {}
    addEntry := fun d e => d.insert e
  }

def registerAutoAttr (attrName : Name) (attrDescr : String) (extName : Name := attrName.appendAfter "Ext") : IO AutoExtension := do
  let ext ← mkAutoExt extName
  mkAutoAttr attrName attrDescr ext
  return ext

initialize autoExtension : AutoExtension ← registerAutoAttr `auto "auto closing lemma"

-- initialize autoLemmasAttr : TagAttribute ← registerTagAttribute `auto "auto lemmas"
-- initialize autoLemmasAttr : ParametricAttribute Unit ←
--   registerAutoAttribute {
--     name := `auto,
--     descr := "auto lemmas",
--     getParam := λ _ _ => () }
open Lean
-- open Tactic
open Lean Meta

-- initialize extLemmasCache : DeclCache (DiscrTree Name) ←
--   DeclCache.mk "ext: initialize cache" {} fun decl ci lemmas => do
--     if let some keys := extAttribute.getParam (← getEnv) decl then
--       lemmas.insertCore keys decl
--     else
--       lemmas

def getAutoLemmas [Monad m] [MonadEnv m] : m NameSet := do
  let ns := autoExtension.getState (← getEnv)
  return ns
    |>.insert ``True.intro
    |>.insert ``Iff.intro
    |>.insert ``And.intro

def getAutoList [Monad m] [MonadEnv m] (hyps : Array Name := #[]) : m (Array Name) := do
  return hyps ++ (← getAutoLemmas).toArray

initialize registerTraceClass `auto
initialize registerTraceClass `auto.apply
initialize registerTraceClass `auto.apply.attempts
initialize registerTraceClass `auto.apply.failure
initialize registerTraceClass `auto.destruct_hyp
initialize registerTraceClass `auto.goal
initialize registerTraceClass `auto.iterate
initialize registerTraceClass `auto.lemmas

open Lean

def Meta.applyAuto (ns : Array Name) (allowMVars := false) : SearchTacticM δ Unit :=
SearchTacticM.focus do
  let n ← SearchT.pick' ns
  traceM `auto.lemmas <| return s!"Lemma: {n}"
  let mut lmm ← (mkConstWithFreshMVarLevels n : TacticM _)
  Lean.Elab.Term.synthesizeSyntheticMVars true
  lmm ← instantiateMVars lmm
  liftMetaTactic (applyUnifyAll . lmm allowMVars)

def Meta.applyAssumption (allowMVars := false) : SearchTacticM δ Unit := SearchTacticM.focus $ do
  let x ← SearchT.pick' (← getLCtx).getFVarIds
  let lctx ← getLCtx
  guard (¬ (lctx.get! x).isAuxDecl)
  traceM `auto.lemmas <| return s!"Hyp: {lctx.get! x |>.userName}"
  liftMetaTactic (applyUnifyAll . (mkFVar x) allowMVars)

elab "#print" "auto_db" : command => do
  IO.println (← getAutoLemmas).toList

instance : ToMessageData LocalContext where
  toMessageData lctx := toMessageData
    <| lctx.fvarIdToDecl.toList.map
    <| LocalDecl.userName ∘ Prod.snd

def Meta.destructHyp : TacticM Unit := focus $ do
  let lctx ← getLCtx
  let mut changed := false
  trace[auto.destruct_hyp] "local context: {lctx}"
  for x in lctx do
    trace[auto.destruct_hyp]"local: {x.userName}"
    trace[auto.destruct_hyp]"is type: {x.type}"
    let type ← instantiateMVars x.type
    if ¬ x.isAuxDecl ∧ type.isAppOf ``And then
      let g ← getMainGoal
      let gs ← cases g x.fvarId
      replaceMainGoal <|
        gs.toList.map <|
          InductionSubgoal.mvarId ∘ CasesSubgoal.toInductionSubgoal
      changed := true
  guard changed

section HOrElse
variable  [Alternative m] [Monad m] [MonadBacktrack σ m]
instance : HOrElse (m α) (SearchT δ m α) (SearchT δ m α) where
  hOrElse x y := (Alternative.orElse (liftM x) y)

instance : HOrElse (SearchT δ m α) (m α) (SearchT δ m α) where
  hOrElse x y := (Alternative.orElse x (liftM ∘ y))

end HOrElse

def withMainContext' (x : SearchTacticM δ α) : SearchTacticM δ α :=
λ f => withMainContext (x f)

def Meta.tacAutoStep (ns : Array Name) (allowMVars := false) : SearchTacticM δ Unit :=
withMainContext' $
  Lean.Elab.Tactic.tacRefl <|>
  liftMetaTactic (do Meta.contradiction .; return []) <|>
  Meta.applyAssumption allowMVars <|>
  Meta.destructHyp <|>
  liftMetaTactic1 ((some ∘ Prod.snd) <$> intro1 .) <|>
  Meta.applyAuto (allowMVars := allowMVars) ns
  -- Meta.applyAuto ns allowMVars <|>
  -- liftMetaTactic1 ((some ∘ Prod.snd) <$> intro1 .)

def Meta.tacAuto (ns : Array Name) (bound : Option Nat)
  (allowMVars := false) : SearchTacticM δ Unit :=
let bound := bound.getD 5
SearchTacticM.focusAndDone $
iterate bound <| Meta.tacAutoStep ns allowMVars

elab "destruct_hyp" : tactic => withMainContext Meta.destructHyp

syntax "eauto" "[" ident,* "]" : tactic
syntax "auto" ("[" ident,* "]")? (" with " num)? : tactic

elab "auto" : tactic => do
  withMainContext (Meta.tacAuto (← getAutoList) none).run

elab "auto" " with " n:num : tactic => do
  withMainContext (Meta.tacAuto (← getAutoList) (Syntax.isNatLit? n)).run

elab "auto" "[" ids:ident,* "]": tactic => do
  let ids ← getAutoList (← ids.getElems.mapM resolveGlobalConstNoOverload)
  withMainContext (Meta.tacAuto ids none).run

elab "auto" "[" ids:ident,* "]" " with " n:num : tactic => do
  let ids ← getAutoList (← ids.getElems.mapM resolveGlobalConstNoOverload)
  withMainContext (Meta.tacAuto ids (Syntax.isNatLit? n)).run

elab "eauto" : tactic => do
  withMainContext (Meta.tacAuto (← getAutoList) none true).run
elab "auto_step" : tactic => do
  withMainContext (Meta.tacAutoStep (← getAutoList)).run
elab "eauto_step" : tactic => do
  withMainContext (Meta.tacAutoStep (allowMVars := true) (← getAutoList)).run
elab "apply_auto" : tactic => do
  withMainContext (Meta.applyAuto (← getAutoList)).run

elab "eauto" "[" ids:ident,* "]" : tactic => do
  let ids ← getAutoList (← ids.getElems.mapM resolveGlobalConstNoOverload)
  withMainContext (Meta.tacAuto ids none true).run

elab "eauto" "[" ids:ident,* "]" " with " n:num : tactic => do
  let ids ← getAutoList (← ids.getElems.mapM resolveGlobalConstNoOverload)
  withMainContext (Meta.tacAuto ids (Syntax.isNatLit? n) true).run

syntax "change" term "at" ident : tactic

elab "change" t:term "at" h:ident : tactic =>
  withMainContext do
    let h ← getFVarId h
    liftMetaTactic1 (changeLocalDecl . h (← elabTerm t none))

elab "apply_assumption" : tactic =>
  withMainContext (Meta.applyAssumption true).run


-- macro "auto" : tactic =>
--   `(tactic|
--     solve
--     | repeat
--         first
--         | refl
--         | apply True.intro
--         | assumption
--         | destruct_hyp
--         | apply And.intro
--         | apply Iff.intro
--         | intros _
--         | apply_auto_lemma )

-- macro "auto_step" : tactic =>
--   `(tactic|
--         first
--         | refl
--         | apply True.intro
--         | assumption
--         | destruct_hyp
--         | apply And.intro
--         | apply Iff.intro
--         | intros _
--         | apply_auto_lemma )

-- theorem swapHyp {p q : Prop} (h : p) (h' : ¬ p) : q := by
--   cases h' h

-- macro "swapHyp" h:term "as" h':ident : tactic =>
--   `(tactic| apply Classical.byContradiction; intro $h' <;>
--             first
--             | apply $h ; clear $h
--             | apply swapHyp $h <;> clear $h
--               )

open Lean.Elab.Tactic

elab "all_but_first " tac:tacticSeq : tactic => do
  let mvarId :: mvarIds ← getUnsolvedGoals
    | throwNoGoalsToBeSolved
  let mut gs := #[mvarId]
  for g in mvarIds do
    if ← not <$> isExprMVarAssigned g then
      setGoals [g]
      tryTac <| withMainContext <| evalTactic tac
      gs := gs.appendList (← getGoals)
  setGoals gs.toList

macro:1 x:tactic " </> " y:tactic:0 : tactic =>
  `(tactic| focus ($x:tactic; all_but_first ($y:tactic; done)))

syntax "split" "*" : tactic
macro_rules
  | `(tactic| split*) => `(tactic| first | split <;> split* | skip)

macro "have " " ← " " : " p:term " := " proof:term : tactic =>
  `(tactic|
    have h : $p := $proof ;
    rw [← h] <;> clear h )

macro "have " " → " " : " p:term " := " proof:term : tactic =>
  `(tactic|
    have h : $p := $proof ;
    rw [h] <;> clear h )

namespace Classical

theorem contradiction {p q} (hp : p) (hnp : ¬ p) : q :=
by cases hnp hp

end Classical

macro "falseHyp" h:ident : tactic =>
  `(first
    | refine' Classical.contradiction _ $h; clear $h
    | apply Classical.contradiction $h; clear $h )
