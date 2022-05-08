
import Lib.Meta.About
import Lib.Meta.DeclGraph
import Lib.Meta.Dump
import Lib.Meta

/-- Target of deriving handler -/
def ProjSimps := Unit

namespace Lean.Meta.Simps
open Lean.Elab
open Lean.Elab.Command
-- #fullname CommandElabM
-- #about DefinitionVal
-- #print getStructureFields

-- #check Array.zipWith
-- #print Expr
-- #fullname logInfo

def deriveProjSimpLemmas (n : Name) : MetaM Unit := do
let info ← getConstInfo n
let ls' := info.levelParams
let ls := ls'.map mkLevelParam
let fn := mkConst n ls
let env ← getEnv
let some (.defnInfo dfn) := env.find? n
  | throwError "invalid definition"
let t ← inferType fn
forallTelescope t λ vs t => do
  let lhs := mkAppN fn vs
  let (.const tctor ..) := (← whnf t).getAppFn
    | throwError "'{t}' is not a structure"
  let targs := t.getAppArgs
  let val ← whnf <| mkAppN dfn.value vs
  let some fields := getStructureInfo? env tctor
    | throwError s!"{tctor} is not a structure"
  let valArgs := val.getAppRevArgs.extract 0 fields.fieldInfo.size
  -- let fields := getStructureFields env tctor
  for x in fields.fieldInfo, y in valArgs do
    let lhs := mkApp (← mkAppOptM x.projFn (targs.map .some)) lhs
    let prop ← mkAppM `Eq #[lhs, y]
    let proof ← Meta.mkFreshExprMVar (some prop)
    let prop ← mkForallFVars vs prop
    discard <| apply proof.mvarId! (← mkConstWithFreshMVarLevels ``Eq.refl)

    let proof ← instantiateMVars proof
    let proof ← mkLambdaFVars vs proof
    let thmName := n.appendBefore <| x.fieldName.getString! ++ "_"
    discard <| addThm ls' thmName prop proof
    trace[simps.lemmas]"{thmName} : {← ppExpr prop}"
    addSimpTheorem simpExtension thmName false false .«global» (default)

initialize
  registerTraceClass `simps.lemmas
  registerBuiltinAttribute {
    name := `simps
    descr := "derive simp lemmas to reduce projections applied to a given definition"
    add := λ n _ _ => do
      deriveProjSimpLemmas n |>.run' {} {}  }

end Lean.Meta.Simps
