
import Lean.Elab.Declaration

import Lib.Meta


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
namespace Command

open Elab Elab.Command
open Meta

syntax (name := opaqueDef)
   declModifiers "opaque " «def» : command

initialize registerTraceClass `opaque
initialize registerTraceClass `opaque.decls
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
  let newEqnName := eqnN.replacePrefix name' name
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
  let ppStx ← liftCoreM <| Lean.PrettyPrinter.ppCommand stx
  trace[opaque.decls]"declNamespace: {ns}"
  Lean.Elab.Command.elabDeclaration stx
  let declName   := ns ++ declName
  let insideName := ns ++ insideName
  liftTermElabM none <| constantWrapper declName insideName

end Command
end Parser
end Lean
