import Lean.Meta.Tactic.Split
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Command

class Reflexive (R : α → α → Prop) where
  refl x : R x x

instance : @Reflexive α (.=.) where
  refl _ := rfl

instance : Reflexive (.↔.) where
  refl _ := Iff.rfl

instance : Reflexive (.→.) where
  refl _ := id

instance : @Reflexive Nat LE.le where
  refl := Nat.le_refl

macro "obtain " p:term " from " d:term : tactic =>
  `(tactic| match $d:term with | $p:term => ?_)

macro "left" : tactic =>
  `(tactic| apply Or.inl)

macro "right" : tactic =>
  `(tactic| apply Or.inr)

namespace Lean.Elab.Tactic

initialize registerTraceClass `refl

open Expr Lean.Meta
-- #check @Reflexive.refl
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
    throwError "Expection a reflexive relation: R x y"

end Lean.Elab.Tactic

syntax "refl" : tactic

elab "refl" : tactic => Lean.Elab.Tactic.tacRefl

-- macro "refl" : tactic =>
--   `(tactic| exact Reflexive.refl _)

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

open Lean.Elab.Tactic
open Lean
-- (TagAttribute registerTagAttribute)

syntax (name := auto) "auto" : attr

abbrev AutoExtension := SimpleScopedEnvExtension Name NameSet

def mkAutoAttr (attrName : Name) (attrDescr : String) (ext : AutoExtension) : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    add   := fun declName stx attrKind =>
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        ext.add declName attrKind
      discard <| go.run {} {}
    erase := fun declName => do
      let s ← ext.getState (← getEnv)
      let s ← s.erase declName
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

def registerAutoAttribute {α : Type} [Inhabited α] (impl : ParametricAttributeImpl α) : IO (ParametricAttribute α) := do
  let ext : PersistentEnvExtension (Name × α) (Name × α) (NameMap α) ← registerPersistentEnvExtension {
    name            := impl.name
    mkInitial       := pure {}
    addImportedFn   := fun s => impl.afterImport s *> pure {}
    addEntryFn      := fun (s : NameMap α) (p : Name × α) => s.insert p.1 p.2
    exportEntriesFn := fun m =>
      let r : Array (Name × α) := m.fold (fun a n p => a.push (n, p)) #[]
      r.qsort (fun a b => Name.quickLt a.1 b.1)
    statsFn         := fun s => "parametric attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrImpl : AttributeImpl := {
    name  := impl.name
    descr := impl.descr
    add   := fun decl stx kind => do
      unless kind == AttributeKind.global do throwError "invalid attribute '{impl.name}', must be global"
      let env ← getEnv
      let val ← impl.getParam decl stx
      let env' := ext.addEntry env (decl, val)
      setEnv env'
      try impl.afterSet decl val catch _ => setEnv env
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }


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
  -- let n ← getMainModule
  let d := (← autoExtension.getState (← getEnv))
  return d
  -- .insert ``True.intro ()
  -- let env ← getEnv
  -- let mut ls : NameSet := NameSet.empty
  -- for (n, c) in env.constants.map₁.toList do
  --   if let some z := autoLemmasAttr.getParam env n then
  --     ls := ls.insert n
  -- IO.println ls.toList
  -- let n ← ().mainModule
  -- IO.println $ (← getEnv).getModuleIdxFor? n |>.isSome
  -- return l

initialize registerTraceClass `auto.apply
initialize registerTraceClass `auto.apply.attempts

open Lean
-- @[macro autoAttr] def addAutoLemma : Tactic := fun stx =>
  -- _
-- #exit
-- @[macro applyAutoLemma]
def Meta.applyAuto : TacticM Unit := focusAndDone $ do
  let apply (n : Name) : TacticM Unit := do
      trace[auto.apply.attempts] "try {n}"
      let ls ← Lean.Meta.apply (← getMainGoal) (← mkConstWithLevelParams n)
      trace[auto.apply] "apply: {n}"
      -- guard ls.isEmpty <|>
        -- throwError "no meta variables should remain {ls.length}"
      replaceMainGoal ls
  trace[auto.apply]"{(← getAutoLemmas).size} candidates"
  (← getAutoLemmas).toList.firstM apply

-- attribute [auto] And.intro

elab "#print_auto_db" : command => do
  IO.println (← getAutoLemmas).toList

elab "apply_auto_lemma" : tactic => withMainContext Meta.applyAuto

-- #exit
-- example : True :=
-- by apply_auto_lemma

initialize registerTraceClass `auto.destruct_hyp

instance : ToMessageData LocalContext where
  toMessageData lctx := toMessageData
    <| lctx.fvarIdToDecl.toList.map
    <| LocalDecl.userName ∘ Prod.snd

def Meta.destructHyp : TacticM Unit := focus $ do
  let lctx ← getLCtx
  let mut changed := false
  -- let xs := [ x <- lctx]
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
  -- return ()

elab "destruct_hyp" : tactic => withMainContext Meta.destructHyp

  -- destruct_hyp

-- #exit
-- example : True := by apply_auto_lemma
-- #exit
initialize registerTraceClass `auto

macro "auto" : tactic =>
  `(tactic|
    solve
    | repeat
        first
        | refl
        | apply True.intro
        | assumption
        | destruct_hyp
        | apply And.intro
        | apply Iff.intro
        | intros _
        | apply_auto_lemma )

macro "auto_step" : tactic =>
  `(tactic|
        first
        | refl
        | apply True.intro
        | assumption
        | destruct_hyp
        | apply And.intro
        | apply Iff.intro
        | intros _
        | apply_auto_lemma )

-- theorem swapHyp {p q : Prop} (h : p) (h' : ¬ p) : q := by
--   cases h' h

-- macro "swapHyp" h:term "as" h':ident : tactic =>
--   `(tactic| apply Classical.byContradiction; intro $h' <;>
--             first
--             | apply $h ; clear $h
--             | apply swapHyp $h <;> clear $h
--               )
