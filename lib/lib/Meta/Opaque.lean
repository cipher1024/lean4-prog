
import Lean.Elab.Declaration

import Lib.Meta

def Option.elim {α β} (x : β) (f : α → β) : Option α → β
| Option.none => x
| Option.some x => f x

structure Locked {α : Sort u} (x : α) where
  val : α
  val_eq : val = x

namespace Lean
namespace Parser
namespace Command

open Elab Elab.Command
open Meta

syntax (name := opaqueDef)
   declModifiers "opaque " «def» : command

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

def constantWrapper (name name' : Name) : MetaM Unit := do
  let ls := (← getConstInfo name').levelParams
  let e ← mkConstWithLevelParams name'

  let t ← inferType e
  let t' ← mkAppOptM ``Locked #[none, e]
  let eqPr ← mkAppOptM ``rfl #[none, e]
  let locked ← mkAppOptM ``Locked.mk #[none, e, e, eqPr]
  let name'' ← addConst ls (name ++ `_locked) t' locked
  trace[opaque.decls]"constant {name''} : {t'} := {locked}"

  let locked_e ← mkConstWithLevelParams name''
  let e' ← mkAppOptM ``Locked.val #[none, none, locked_e]
  trace[opaque.decls]"def {name} : {t} := {e'}"
  discard <| addDef ls name t e'

  let e_def ← mkConstWithLevelParams name
  let pr ← mkAppOptM ``Locked.val_eq #[none, none, locked_e]
  let eqStmt ← mkAppOptM ``Eq #[none, e_def, e]
  let eqThmName := name ++ `_unlock
  trace[opaque.decls]"theorem {eqThmName} : {eqStmt}"
  let eqThm ← addThm ls eqThmName eqStmt pr
  let eqns := (← getEqnsFor? name') |>.getD #[]
  let uEqns : Array Name := (← getUnfoldEqnFor? name')
    |>.elim #[] <| #[].push
  let newEqns ← eqns.mapM (rewriteEqn . name name' eqThm)
  let newUEqns ← uEqns.mapM (rewriteEqn . name name' eqThm)
  pure ()

def replaceName (n n' : Name) (s : Syntax) := Id.run <|
s.replaceM λ s =>
  if s.isIdent && s.getId == n then
    return mkIdentFrom s n'
  else return none

@[commandElab opaqueDef]
def elabOpaqueDef : CommandElab := λ stx => do
  let mods := stx[0]
  let kw := stx[1]
  let «def» := stx[2]
  let name  := «def»[1][0].getId
  let name' := name ++ `_def
  let id    := «def»[1].setArg 0 <| Lean.mkIdent name'
  let «def» := «def».setArg 1 id
  let «def» := replaceName name `_def «def»
  let stx   := mkNode ``Lean.Parser.Command.declaration #[mods, «def»]
  let ppStx ← liftCoreM <| Lean.PrettyPrinter.ppCommand stx
  trace[opaque.decls]"{ppStx}"
  Lean.Elab.Command.elabDeclaration stx
  liftTermElabM none <| constantWrapper name name'

end Command
end Parser
end Lean
