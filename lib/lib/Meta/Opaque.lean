/-
TODO:
  - opaque struct
  - opaque inductive
  - equation tags
  - constructor / recursor tags?
    - use them in pattern matching
    - use them in `induction` / `cases` / `match`

  opaque namespace:
  - including normal namespace
  - including normal section
  - including opaque def


-/
import Lean.Elab.Declaration
import Lean.Elab.Command
import Lean.Elab.BuiltinCommand

import Lib.Meta
import Lib.Meta.TransportFacts


namespace Lean.Syntax

def mkEndNode (ident : Option Name) : Syntax :=
mkNode ``Lean.Parser.Command.end
  #[mkAtom "end", mkOptionalNode <| ident.map mkIdent]

def mkEndNodeFrom (stx : Syntax) (ident : Option Name) : Syntax :=
Syntax.node stx.getHeadInfo ``Lean.Parser.Command.end
  #[mkAtom "end", mkOptionalNode <| ident.map mkIdent]

variable [Monad m] [MonadRef m]

def mkEndNodeFromRef (ident : Option Name) : m Syntax :=
do return mkEndNodeFrom (← getRef) ident

end Lean.Syntax

namespace Lean.Name

def revConcat : List String → Name :=
List.foldl mkStr anonymous

@[specialize]
def withoutPrivatePrefixAux (ns : List String) (f : Name → Name) : Name → Name
| anonymous => f <| revConcat ns
| str p s .. => withoutPrivatePrefixAux (s :: ns) f p
| n@(num p s ..) => n ++ f (revConcat ns)

@[specialize]
def withoutPrivatePrefix (f : Name → Name) : Name → Name :=
withoutPrivatePrefixAux [] f

def replacePrefix' (n p newP : Name) : Name :=
withoutPrivatePrefix (replacePrefix . p newP) n

end Lean.Name

structure Locked {α : Sort u} (x : α) where
  val : α
  val_eq : val = x

namespace Lean

namespace Meta

def addDef' (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
trace[opaque.decls]"def {n} : {t}"
addDef us n t d

def addThm' (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
trace[opaque.decls]"theorem {n} : {t}"
addThm us n t d

def addConst' (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
trace[opaque.decls]"constant {n} : {t}"
addConst us n t d

end Meta

namespace Parser
namespace OpaqueExt

open Lean.Elab.Tactic

structure OpaqueDef where
  declName : Name
  intlName : Name
  eqvProof : Name
  lockedConst : Name
  unfoldEqn : Option Name := none
  eqns : Array Name := #[]
  deriving Inhabited

structure OpaqueDefIdx where
  intlToDecl : NameMap OpaqueDef := {}
  decls : NameMap OpaqueDef := {}
  simpLemmas : Lean.Meta.SimpTheorems := {}
  newLemmas : List Name := []
  deriving Inhabited

namespace OpaqueDefIdx

def insert (o : OpaqueDefIdx) (decl : OpaqueDef) : OpaqueDefIdx where
  intlToDecl := o.intlToDecl.insert decl.intlName decl
  decls := o.intlToDecl.insert decl.declName decl
  simpLemmas := o.simpLemmas
  newLemmas := decl.eqvProof :: o.newLemmas

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
  }

def getOpaqueExtension (ext : OpaqueExtension) : MetaM OpaqueDefIdx := do
return ext.getState (← getEnv)

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
  return ext

end OpaqueExt

initialize opaqueExtension : OpaqueExt.OpaqueExtension ←
  OpaqueExt.registerOpaqueAttr `opaque "opaque definitions"

def getOpaqueExtension :=
OpaqueExt.getOpaqueExtension opaqueExtension

def setOpaqueExtension (idx : OpaqueExt.OpaqueDefIdx) : MetaM Unit :=
modifyEnv λ env => opaqueExtension.modifyState env λ _ => idx

def registerOpaqueDef (decl : OpaqueExt.OpaqueDef) : MetaM Unit :=
modifyEnv (opaqueExtension.addEntry . decl)


def getSimpLemmas : MetaM Meta.SimpTheorems := do
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

initialize registerTraceClass `opaque
initialize registerTraceClass `opaque.decls
initialize registerTraceClass `opaque.parser
initialize registerTraceClass `opaque.debug
initialize registerTraceClass `opaque.proof.state

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
  let newEqnName := eqnN.replacePrefix' name' name
  addThm' ls newEqnName t₀ proof

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
  let lockedName ← addConst' ls (declName ++ `_locked) t' locked

  let locked_e ← mkConstWithLevelParams lockedName
  let e' ← mkAppOptM ``Locked.val #[none, none, locked_e]
  discard <| addDef' ls declName t e'

  let e_def ← mkConstWithLevelParams declName
  let pr ← mkAppOptM ``Locked.val_eq #[none, none, locked_e]
  let eqStmt ← mkAppOptM ``Eq #[none, e_def, e]
  let eqThmName := declName ++ `_unlock
  let eqThm ← addThm' ls eqThmName eqStmt pr
  let eqns := (← getEqnsFor? intlName) |>.getD #[]
  let uEqns : Option Name ← getUnfoldEqnFor? intlName
  let newEqns  ← eqns.mapM (rewriteEqn . declName intlName eqThm)
  let newUEqns ← uEqns.mapM (rewriteEqn . declName intlName eqThm)
  let t ← mkAppOptM ``Transport.EqvTerm
    #[none, none, mkConst declName ls', mkConst intlName ls']
  let eqC := mkConst eqThm ls'
  let eqvInst ← mkAppOptM ``Transport.EqvTerm.ofEq #[none, none, none, eqC]
  let inst ← addDef' ls (declName ++ `instEqvTerm) t eqvInst
  addInstance inst AttributeKind.«global» 0

  let opDef : OpaqueExt.OpaqueDef :=
    { declName := declName,
      intlName := intlName,
      eqvProof := eqThm,
      lockedConst := lockedName,
      eqns := newEqns,
      unfoldEqn := newUEqns }
  registerOpaqueDef opDef
  pure ()

def replaceName (n n' : Name) (s : Syntax) := Id.run <|
s.replaceM λ s =>
  if s.isIdent && s.getId == n then
    return mkIdentFrom s n'
  else return none

section Name
open Name

def mkImplName : Name → Name
| str p s _ => p ++ mkSimple s ++ `_impl ++ mkSimple s
| n => n

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
  let stx   := mkNode ``Lean.Parser.Command.declaration #[mods, «def»]
  trace[opaque.decls]"declNamespace: {ns}"
  Lean.Elab.Command.elabDeclaration stx
  let declName   := ns ++ declName
  let insideName := ns ++ insideName
  liftTermElabM none <| constantWrapper declName insideName

end Command
namespace Transport

open OpaqueExt

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

def showProofState : TacticM MessageData := do
let gs ← getGoals
let mut res : Format := s!"Goals ({gs.length})"
for g in gs do
  let g ← Meta.ppGoal g
  res := res ++ "\n\n" ++ g
return res

def proveTransport (g : Expr) : TermElabM Expr := do
let g ← mkFreshExprMVar g
discard <| Tactic.run g.mvarId! do
  trace[opaque.proof.state]"begin proof"
  repeat do
    traceM `opaque.proof.state showProofState
    discard (liftMetaTactic1' (intro . `_))  <|>
      liftMetaTactic1 (do Meta.assumption .; pure none) <|>
      liftMetaTactic (Meta.applyc . ``Transport.refl) <|>
      liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_arrow) <|>
      liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_forall') <|>
      liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_forall) <|>
      liftMetaTactic (Meta.applyc . ``Transport.EqvTerm_app) <|>
      liftMetaTactic (Meta.applyc . ``Transport.EqvTerm_app') <|>
      liftMetaTactic (Meta.applyc . ``Transport.EqvTypes_of_EqvTerm) <|>
      liftMetaTactic (Meta.applyc . ``inferInstance)
  until (← getGoals).isEmpty
  let gs ← getUnsolvedGoals
  done
  trace[opaque.proof.state]"end proof"
return g

def transportDecl (declName intlName : Name) (isThm : Bool) : MetaM Unit := do
  trace[opaque.debug]"begin {declName} ({intlName})"
  let c  ← mkConstWithLevelParams intlName
  let t  ← inferType c
  let t' ← transportType t
  let e ← mkAppOptM ``Transport.mkLockedType #[t',none,c]
  let argT := (← inferType e).bindingDomain!
  trace[opaque.debug]"begin transport proof"
  let transPr ← proveTransport argT |>.run'
  trace[opaque.debug]"end transport proof"
  let pr := mkApp e transPr
  let ls  := (← getConstInfo intlName) |>.levelParams
  let ls' := ls.map mkLevelParam
  let prT ← inferType pr
  let pr' ← instantiateMVars pr
  let lockedDecl ← addConst' ls (declName ++ `_locked)
      (← inferType pr) pr
  let lockedC := mkConst lockedDecl ls'
  let e ← mkAppOptM ``LockedType.val
    #[none, none, none, lockedC]
  if isThm
    then discard <| addThm' ls declName t' e
    else discard <| addDef' ls declName t' e

  let declC := mkConst declName ls'
  let intlC := mkConst intlName ls'
  let e ← mkAppOptM ``LockedType.val_eqv #[none, none, none, lockedC]
  let heq ← mkAppOptM ``HEq #[none, declC, none, intlC]
  let unlock ← addThm' ls (declName ++ `_unlock) heq e

  let instT ← mkAppOptM ``Transport.EqvTerm
    #[none,none,declC,intlC]
  let heqPr := mkConst unlock ls'
  let instPr ← mkAppOptM ``Transport.EqvTerm.ofHEq
    #[none,none,none,none,heqPr]
  let inst ← addThm' ls (declName ++ `instEqvTerm) instT instPr
  addInstance inst AttributeKind.«global» 0

  let opDef : OpaqueExt.OpaqueDef :=
    { declName := declName,
      intlName := intlName,
      eqvProof := unlock,
      lockedConst := lockedDecl,
      eqns := #[],
      unfoldEqn := none }
  registerOpaqueDef opDef
  trace[opaque.debug]"end {declName} ({intlName})"

open Lean.Elab.Command

private def removeImpl : Name → Name
| Name.str p s _ =>
  if s == "_impl" then p
  else removeImpl p
| n => n

def elabAndTransport (_ : Name) (d : Syntax) : CommandElabM Unit := do
let ns ← getCurrNamespace
let «def» := d.getArgs[1]
let kind := «def».getKind
let rawName := «def»[1][0].getId
let intlName := ns ++ rawName
let declName := removeImpl ns ++ rawName
trace[opaque.parser]"decl kind:   {d.getKind}"
trace[opaque.parser]"inside kind: {«def».getKind}"
elabDeclaration d
let fullName ← resolveGlobalConstNoOverload <| Lean.mkIdent intlName
if isPrivateName fullName then
  pure ()
else if kind == `Lean.Parser.Command.def then
  liftCoreM <| transportDecl declName intlName false |>.run'
else if kind == `Lean.Parser.Command.theorem then
  liftCoreM <| transportDecl declName intlName true |>.run'
else
  throwError "not supported"

open Lean.Syntax
def myElabEnd (n : Name) : CommandElabM Unit := do
elabEnd (← mkEndNodeFromRef <| some <| n ++ `_impl ++ n  )

macro "opaque " "namespace " id:ident : command => do
  let idImplName := Lean.mkIdent <| id.getId ++ `_impl
  let defName := Lean.mkIdent <| id.getId ++ `_impl ++ id.getId
  let implName := Lean.mkIdent `_impl
  let idStr := Lean.Syntax.mkStrLit id.getId.toString
  let command := Lean.mkIdent `command
  let declaration := Lean.mkIdent ``Lean.Parser.Command.declaration
  let idLit := Lean.Syntax.mkNameLit <| toString id
  let implNLit := Lean.Syntax.mkNameLit "_impl"
  `(
    #quiet check $defName:ident

    namespace $idImplName:ident
    namespace $(Lean.mkIdent id.getId):ident

    local elab d:($declaration:ident) : $command =>
      elabAndTransport $idLit:name d

    -- local elab_rules : $command
    -- | `($$d:declaration) => elabAndTransport $idLit:nameLit

    local elab "end" id:ident : $command:ident => myElabEnd id.getId

    -- local elab_rules : $command
    -- | `(end $$id:ident) => myElabEnd id.getId

    local elab "section" id:(ident)? : $command =>
      throwError "section and namespaces not supported in opaque namespaces"

    local elab "namespace" id:(ident)? : $command =>
      throwError "section and namespaces not supported in opaque namespaces"

    -- local elab_rules : $command
    -- | `(section $$id) =>
    --   throwError "section and namespaces not supported in opaque namespaces"

    -- local elab_rules : $command
    -- | `(namespace $$id) =>
    --   throwError "section and namespaces not supported in opaque namespaces"

  )

end Transport
end Parser
end Lean
