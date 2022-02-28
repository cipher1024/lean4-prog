
import Lean.Elab.Declaration
import Lean.Elab.Command
import Lean.Elab.BuiltinCommand

import Lib.Meta
import Lib.Meta.Dump
import Lib.Meta.TransportFacts

namespace Option

def elim {α β} (x : β) (f : α → β) : Option α → β
| none => x
| some x => f x

end Option

namespace Std.AssocList

variable [DecidableEq α]

def eraseAll (x : α) : AssocList α β → AssocList α β
| nil => nil
| cons k v xs =>
  let xs' := eraseAll x xs
  if x = k then xs'
  else cons k v xs'

end Std.AssocList

namespace Lean.Meta

def applyc (g : MVarId) (n : Name) : MetaM (List MVarId) := do
apply g (← mkConstWithFreshMVarLevels n)

end Lean.Meta

structure Locked {α : Sort u} (x : α) where
  val : α
  val_eq : val = x

namespace Lean
namespace Parser
namespace OpaqueExt

open Lean.Elab.Tactic
open Lean

structure OpaqueDef where
  declName : Name
  intlName : Name
  eqvProof : Name
  lockedConst : Name
  unfoldEqn : Option Name := none
  eqns : Array Name := #[]
  deriving Inhabited

-- #check Lean.Meta.simp
-- #check Lean.Meta.SimpTheorems

structure OpaqueDefIdx where
  intlToDecl : NameMap OpaqueDef := {}
  decls : NameMap OpaqueDef := {}
  simpLemmas : Lean.Meta.SimpTheorems := {}
  newLemmas : List Name := []
  -- newLemmas : Std.AssocList Name Name := Std.AssocList.nil
  deriving Inhabited

namespace OpaqueDefIdx

def insert (o : OpaqueDefIdx) (decl : OpaqueDef) : OpaqueDefIdx where
  intlToDecl := o.intlToDecl.insert decl.intlName decl
  decls := o.intlToDecl.insert decl.declName decl
  simpLemmas := o.simpLemmas
  newLemmas := decl.eqvProof :: o.newLemmas
  -- newLemmas := Std.AssocList.cons decl.intlName decl.eqvProof o.newLemmas
  -- simpLemmas := (← o.simpLemmas.addConst (inv := true) decl.eqvProof) }

def erase (o : OpaqueDefIdx) (decl : Name) : OpaqueDefIdx := Id.run do
let some d := o.decls.find? decl
  | return o
return {
  decls := o.decls.erase decl
  intlToDecl := o.intlToDecl.erase d.intlName
  simpLemmas := o.simpLemmas.eraseCore d.eqvProof
  newLemmas := o.newLemmas.erase d.eqvProof
  }

end OpaqueDefIdx

abbrev OpaqueExtension :=
SimpleScopedEnvExtension OpaqueDef OpaqueDefIdx


def mkOpaqueExt (extName : Name) : IO OpaqueExtension :=
  registerSimpleScopedEnvExtension {
    name     := extName
    initial  := {}
    addEntry := fun d decl => d.insert decl
    -- addEntry := fun d e => d.insert e
  }

def getOpaqueExtension (ext : OpaqueExtension) : MetaM OpaqueDefIdx := do
return ext.getState (← getEnv)
-- return ext.getState env

def getEqnsForOpaqueDef (ext : OpaqueExtension) (n : Name) : MetaM (Option (Array Name)) := do
return (← getOpaqueExtension ext)
  |>.decls
  |>.find? n
  |>.map (·.eqns)

def getUnfoldEqnsForOpaqueDef (ext : OpaqueExtension) (n : Name) : MetaM (Option Name) := do
return (← getOpaqueExtension ext)
  |>.decls
  |>.find? n
  |>.bind (·.unfoldEqn)

def registerOpaqueAttr (attrName : Name) (attrDescr : String) (extName : Name := attrName.appendAfter "Ext") : IO OpaqueExtension := do
  let ext ← mkOpaqueExt extName
  Lean.Meta.registerGetEqnsFn <| getEqnsForOpaqueDef ext
  Lean.Meta.registerGetUnfoldEqnFn <| getUnfoldEqnsForOpaqueDef ext
  -- mkOpaqueAttr attrName attrDescr ext
  return ext

end OpaqueExt

initialize opaqueExtension : OpaqueExt.OpaqueExtension ← OpaqueExt.registerOpaqueAttr `opaque "opaque definitions"

def getOpaqueExtension :=
OpaqueExt.getOpaqueExtension opaqueExtension

def setOpaqueExtension (idx : OpaqueExt.OpaqueDefIdx) : MetaM Unit :=
modifyEnv λ env => opaqueExtension.modifyState env λ _ => idx

def registerOpaqueDef (decl : OpaqueExt.OpaqueDef) : MetaM Unit := do
-- let env ← getEnv
modifyEnv (opaqueExtension.addEntry . decl)


def getSimpLemmas : MetaM Meta.SimpTheorems := do
-- let simps
let ext ← getOpaqueExtension
let mut simpLemmas := ext.simpLemmas
for eqn in ext.newLemmas do
  simpLemmas ← simpLemmas.addConst (inv := true) eqn
setOpaqueExtension <| { ext with
  newLemmas := []
  simpLemmas := simpLemmas }
return simpLemmas


namespace Command

open Elab Elab.Command
open Meta

syntax (name := opaqueDef)
   declModifiers "opaque " «def» : command

-- opaque struct, instance, inductive

initialize registerTraceClass `opaque
initialize registerTraceClass `opaque.decls

def proveNewEqn (t₀ : Expr) (eqnN name name' defN : Name) : MetaM Name := do
let eqn ← mkConstWithLevelParams eqnN
let ls := (← getConstInfo eqnN).levelParams
forallTelescope t₀ λ vs t => do
  let proof := (← mkFreshExprMVar t) |>.mvarId!
  let r ← rewrite proof t (← mkConstWithFreshMVarLevels defN)
  let rule ← mkAppOptM ``Eq.mpr #[none, none, r.eqProof]
  let [v] ← apply proof rule
    | throwError "too many goals"
  let [] ← apply v (← mkConstWithFreshMVarLevels eqnN)
    | throwError "too many goals"
  let proof ← mkLambdaFVars vs (mkMVar proof)
  let newEqnName := eqnN.replacePrefix name' name
  trace[opaque.decls] "theorem {newEqnName} : {t}"
  addThm ls newEqnName t₀ proof

def rewriteEqn (eqn name name' eqThm : Name) : MetaM Name := do
let eqnE ← mkConstWithLevelParams eqn
let t ← inferType eqnE
let c ← mkConstWithLevelParams name
let c' ← mkConstWithLevelParams name'
let t := t.replace λ e => if e == c' then some c else none
proveNewEqn t eqn name name' eqThm

def constantWrapper (declName intlName : Name) : MetaM Unit := do
  let ls := (← getConstInfo intlName).levelParams
  let ls' := ls.map mkLevelParam
  let e ← mkConstWithLevelParams intlName

  let t ← inferType e
  let t' ← mkAppOptM ``Locked #[none, e]
  let eqPr ← mkAppOptM ``rfl #[none, e]
  let locked ← mkAppOptM ``Locked.mk #[none, e, e, eqPr]
  -- trace[opaque.decl]"foo {lockedName}"
  let lockedName ← addConst ls (declName ++ `_locked) t' locked
  trace[opaque.decls]"constant {lockedName} : {t'} := {locked}"

  let locked_e ← mkConstWithLevelParams lockedName
  let e' ← mkAppOptM ``Locked.val #[none, none, locked_e]
  trace[opaque.decls]"def {declName} : {t} := {e'}"
  discard <| addDef ls declName t e'

  let e_def ← mkConstWithLevelParams declName
  let pr ← mkAppOptM ``Locked.val_eq #[none, none, locked_e]
  let eqStmt ← mkAppOptM ``Eq #[none, e_def, e]
  let eqThmName := declName ++ `_unlock
  trace[opaque.decls]"theorem {eqThmName} : {eqStmt}"
  let eqThm ← addThm ls eqThmName eqStmt pr
  let eqns := (← getEqnsFor? intlName) |>.getD #[]
  -- let uEqns : Array DeclName := (← getUnfoldEqnFor? intlName)
  let uEqns : Option Name ← getUnfoldEqnFor? intlName
    -- |>.elim #[] <| #[].push
  let newEqns  ← eqns.mapM (rewriteEqn . declName intlName eqThm)
  let newUEqns ← uEqns.mapM (rewriteEqn . declName intlName eqThm)
  let t ← mkAppOptM ``Transport.EqvTerm
    #[none, none, none, mkConst declName ls', mkConst intlName ls']
  let eqC := mkConst eqThm ls'
  -- let eqSymm ←  mkAppOptM ``Eq.symm #[none,none,none,mkConst eqThm ls']
  let eqvInst ← mkAppOptM ``Transport.EqvTerm.ofEq #[none, none, none, eqC]
  let inst ← addDef ls (declName ++ `instEqvTerm) t eqvInst
  addInstance inst AttributeKind.«global» 0
  print_vars![withType eqvInst]

  let opDef : OpaqueExt.OpaqueDef :=
    { declName := declName,
      intlName := intlName,
      eqvProof := eqThm,
      lockedConst := lockedName,
      eqns := newEqns,
      unfoldEqn := newUEqns }
  registerOpaqueDef opDef
  pure ()

#check @Transport.EqvTerm.ofEq

def replaceName (n n' : Name) (s : Syntax) := Id.run <|
s.replaceM λ s =>
  if s.isIdent && s.getId == n then
    return mkIdentFrom s n'
  else none
-- #check @mkDeclName

section Name
open Name

def mkImplName : Name → Name
| str p s _ => p ++ mkSimple s ++ `_impl ++ mkSimple s
| n => n

#eval mkImplName `a.b.c

end Name

@[commandElab opaqueDef]
def elabOpaqueDef : CommandElab := λ stx => do
  let mods := stx[0]
  let kw := stx[1]
  let «def» := stx[2]
  let declName  := «def»[1][0].getId
  let ns ← getCurrNamespace
  let insideName := mkImplName declName
  trace[opaque.decls]"impl name: {insideName}"
  let id    := «def»[1].setArg 0 <| Lean.mkIdent insideName
  let «def» := «def».setArg 1 id
  -- let «def» := replaceName declName `_def «def»
  let stx   := mkNode ``Lean.Parser.Command.declaration #[mods, «def»]
  let ppStx ← liftCoreM <| Lean.PrettyPrinter.ppCommand stx
  trace[opaque.decls]"{ppStx}"
  -- let n ← runTermElabM (some declName) λ _ => do
    -- mkDeclDeclName (← getCurrDeclNamespace) {} declName
  -- trace[opaque.decls]"declName: {declName}"
  trace[opaque.decls]"declNamespace: {ns}"
  Lean.Elab.Command.elabDeclaration stx
  let declName   := ns ++ declName
  let insideName := ns ++ insideName
  liftTermElabM none <| constantWrapper declName insideName

end Command
namespace Transport

open OpaqueExt

-- #fullname liftTermElabM
-- #fullname AttrM
-- #pred Lean.AttrM
-- #pred Lean.CoreM
-- #path Lean.Elab.Term.TermElabM Lean.CoreM
-- #succ Lean.Elab.Term.TermElabM
-- #check Lean.AttrM

-- #path Syntax Format

-- #check Lean.Syntax.formatStx
-- #check Lean.Syntax.prettyPrint
-- #fullname liftMetaM
-- #check Lean.Meta.liftMetaM

-- #fullname rewriteExpr
-- #find prefix replace
-- #check Lean.Expr.replace
-- elab_rules : command
-- | `($d:declaration) => println!"my elab"
-- let env ← getEnv

def transportType (e : Expr) : MetaM Expr := do
let idx ← getOpaqueExtension
return e.replace λ
  | (Expr.const n ls _) =>
    match idx.intlToDecl.find? n with
    | some d => mkConst d.declName ls
    | none => none
  | _ => none

open Lean.Meta
open Transport
open Lean.Elab
open Lean.Parser.Tactic
open Lean.Elab.Tactic
open Lean.Elab.Term
-- #check LockedType
-- #check @Transport.mkLockedType
-- #fullname TacticM
-- #check TacticM
-- #find prefix repeat
-- #fullname first
-- #find prefix first

partial def repeat (tac : TacticM Unit) : TacticM Unit := do
let b ← tryTactic tac
if b then repeat tac
else return ()

def liftMetaTactic1' (tac : MVarId → MetaM (α × MVarId)) : TacticM α := do
let (x, g) ← liftMetaMAtMain (tac .)
replaceMainGoal [g]
return x

def proveTransport (g : Expr) : TermElabM Expr := do
let g ← mkFreshExprMVar g
discard <| Tactic.run g.mvarId! do
  repeat <| withMainContext do

    let g ← getMainTarget
    -- print_vars! [g]
    discard (liftMetaTactic1' intro1) <|>
    liftMetaTactic1 (do Meta.assumption .; return none) <|>
    liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_arrow) <|>
    liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_forall) <|>
    liftMetaTactic (Meta.applyc . ``Transport.EqvTerm_app) <|>
    liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_of_EqvTerm) <|>
    liftMetaTactic (Meta.applyc . ``inferInstance)
  let gs ← getUnsolvedGoals
  for g in gs do
    print_vars![asGoal g]
    -- setGoals [g]
    -- liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_arrow)
  done
-- intro1
-- guard gs.isEmpty <|> throwError "cannot generate complete proof"
-- print_vars! [withType g]
instantiateMVars g

    -- solve
    -- | repeat
    --     first
    --     | intros _
    --     | assumption
    --     | apply EqvTypes_arrow
    --     | apply EqvTypes_forall
    --     | apply EqvTerm_app
    --     | apply EqvTypes_of_EqvTerm
    --     | exact inferInstance )

-- def listMVars (e : Expr) : List MVarId :=
-- Expr.replace

-- #find prefix isArrow
-- #check Lean.Expr.isArrow
def transportDecl (declName intlName : Name) : MetaM Unit := do
        let c  ← mkConstWithLevelParams intlName
        let t  ← inferType c
        let t' ← transportType t
        print_vars![t', t]
        -- let v  ← mkFreshExprMVar none
        let e ← mkAppOptM ``Transport.mkLockedType #[t',none,c]
        let argT := (← inferType e).bindingDomain!
        print_vars![argT]
        -- let e := e.bindingDomain!
        let transPr ← proveTransport argT |>.run'
        let pr := mkApp e transPr
        -- print_vars![t, withType pr]
        let ls  := (← getConstInfo intlName) |>.levelParams
        let ls' := ls.map mkLevelParam
        print_vars![t']
        -- print_vars![t, t', withType e, argT, withType pr]
        println!"*** ABC ***"
        let prT ← inferType pr
        let pr' ← instantiateMVars pr
        let mvars := (← getMVarsNoDelayed pr).map asGoal
        print_vars![prT, prT.hasMVar, pr.hasMVar, pr'.hasMVar, mvars]
        let lockedDecl ← addConst ls (declName ++ `_locked)
            (← inferType pr) pr
        println!"*** ABC ***"
        -- TODO: decl, eqv thm, EqvTerm instance, add in extension
        let lockedC := mkConst lockedDecl ls'
        let e ← mkAppOptM ``LockedType.val
          #[none, none, none, lockedC]
        discard <| addDef ls declName t' e
        let declC := mkConst declName ls'
        let intlC := mkConst intlName ls'
        let e ← mkAppOptM ``LockedType.val_eqv #[none, none, none, lockedC]
        let heq ← mkAppOptM ``HEq #[none, declC, none, intlC]
        print_vars![heq, withType e]
        let unlock ← addThm ls (declName ++ `_unlock) heq e

        println!"*** B ***"
        print_vars![withType declC, withType intlC]
        let instT ← mkAppOptM ``Transport.EqvTerm
          #[none,none,transPr,declC,intlC]
        print_vars![instT]
        println!"*** C ***"
        let heqPr := mkConst unlock ls'
        println!"*** A ***"
        print_vars![asConst ``Transport.EqvTerm.ofHEq, typeOf transPr, typeOf heqPr]
        let instPr ← mkAppOptM ``Transport.EqvTerm.ofHEq
          #[none,none,transPr,none,none,heqPr]
        println!"*** C ***"
        let inst ← addThm ls (declName ++ `instEqvTerm) instT instPr
        addInstance inst AttributeKind.«global» 0
        println!"*** D ***"

        let opDef : OpaqueExt.OpaqueDef :=
          { declName := declName,
            intlName := intlName,
            eqvProof := unlock,
            lockedConst := lockedDecl,
            eqns := #[],
            unfoldEqn := none }
        registerOpaqueDef opDef


        print_vars![asConst lockedDecl, asConst declName,
                    asConst unlock, asConst inst]

-- #check @Transport.EqvTerm
-- #check @HEq.symm
#check @Transport.EqvTerm.ofHEq


open Lean.Elab.Command

private def removeImpl : Name → Name
| Name.str p _ _ => p
| n => n

def elabAndTransport (n : Name) (d : Syntax) : CommandElabM Unit := do
let ns ← getCurrNamespace
let «def» := d.getArgs[1]
let kind := «def».getKind
let rawName := «def»[1][0].getId
let intlName := ns ++ rawName
let declName := removeImpl ns ++ rawName
elabDeclaration d
if kind == `Lean.Parser.Command.def then
  print_vars![ns, intlName, declName]
-- let opName := stx.getArg 1 |>.getId
-- println!"id: {opName}"
  liftCoreM <| transportDecl declName intlName |>.run'

println!"hello {n}"

-- #find prefix ela
-- #check Lean.Elab.Command.elabEnd

def myElabEnd (n : Name) : CommandElabM Unit := do
-- λ s => println!"my end elab"
elabEnd (← `(end $(Lean.mkIdent <| n ++ `_impl):ident))

macro "opaque " "namespace " id:ident : command => do
  let implName := Lean.mkIdent <| id.getId ++ `_impl
  let idStr := Lean.Syntax.mkStrLit id.getId.toString
  -- let defName := Lean.mkIdent <| id.getId ++ `_def
  let command := Lean.mkIdent `command
  let idLit := Lean.Syntax.mkNameLit <| toString id
  let implNLit := Lean.Syntax.mkNameLit "_impl"
  `(

    namespace $implName:ident
    -- local notation $idStr => $defName
    local elab_rules : $command
    | `($$d:declaration) => elabAndTransport $idLit:nameLit d

    -- not working
    local elab_rules : $command
    | `(end $$id') => Lean.Parser.Transport.myElabEnd id'.getId
    -- | s@`(end $$id') => elabEnd <| id' ++ $implNLit:nameLit

    )

-- #fullname command

-- #pred AttrM
-- #check AttrM
def mkOpaqueAttr (attrName : Name) (attrDescr : String) (ext : OpaqueExtension) : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    add   := fun implName stx attrKind => do
        -- let t ← Lean.Meta.MetaM.run'  `(attr| transport id)
        if stx.getNumArgs != 2 then
          throwError "bad syntax"
        let opName := stx.getArg 1 |>.getId
        println!"id: {opName}"
        transportDecl opName implName |>.run'
        -- Command.constantWrapper opDecl implName  |>.run'
        -- | _ =>
          -- let kinds := stx.getKind :: (stx.getArgs.map (·.getKind)).toList
          -- throwError "bad syntax for `transport`: {stx.prettyPrint}\n{kinds}"
    erase := fun declName => do
      let s := ext.getState (← getEnv)
      let s := s.erase declName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }

syntax (name := transport) "transport" ident : attr

initialize
  mkOpaqueAttr `transport "descr" opaqueExtension


end Transport


end Parser
end Lean
