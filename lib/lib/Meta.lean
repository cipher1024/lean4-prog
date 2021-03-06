import Lean.Elab.PreDefinition
import Lean.Meta.Constructions

namespace Lean.Syntax
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

def exprToSyntax (e : Expr) : Elab.TermElabM Syntax :=
Lean.MonadQuotation.withFreshMacroScope do
  let mvar ← Term.elabTerm (← `(?m)) none
  assignExprMVar mvar.mvarId! e
  `(?m)

end Lean.Syntax

namespace Lean.Meta
open Lean Lean.Elab Lean.Elab.Tactic

@[inline]
def liftMetaTactic1' (tac : MVarId → MetaM (α × MVarId)) : TacticM α := do
let (x, g) ← liftMetaMAtMain tac
replaceMainGoal [g]
return x

def instantiateBVarAux (i : Nat) (vs : List Expr) (e : Expr) :
  Expr :=
if e.looseBVarRange = 0 then e else
  match e with
  | Expr.forallE n d b data =>
    mkForall n data.binderInfo
      (instantiateBVarAux i vs d)
      (instantiateBVarAux (i+1) vs b)
  | Expr.lam n d b data     =>
    mkLambda n data.binderInfo
      (instantiateBVarAux i vs d)
      (instantiateBVarAux (i+1) vs b)
  | Expr.mdata m e d        =>
    mkMData m (instantiateBVarAux i vs e)
  | Expr.letE n t v b data  =>
    mkLet n
      (instantiateBVarAux i vs t)
      (instantiateBVarAux i vs v)
      (instantiateBVarAux (i+1) vs b)
  | Expr.app f a data       =>
    mkApp
      (instantiateBVarAux i vs f)
      (instantiateBVarAux i vs a)
  | Expr.proj r j e data    =>
    mkProj r j (instantiateBVarAux i vs e)
  | e@(Expr.bvar j _)  =>
    vs.getD (j - i) e
  | e                       => e

def instantiateBVar (vs : List Expr) (e : Expr) : Expr :=
instantiateBVarAux 0 vs e

section Monad

variable {m} [Monad m] [MonadControlT MetaM m]

@[specialize]
def mkFieldTypeAux
  (vs : List Expr) (s' : Name) :
  Expr →
  (f : List Expr → Expr → m α) →
  m α
| Expr.forallE n d b data, f  => do
  let d := instantiateBVar vs d
  Lean.Meta.withLocalDecl n data.binderInfo d λ v => do
    -- let v' := instantiateBVar vs v
    if d.isConstOf s'
    then f (v :: vs)
          <| instantiateBVar (v :: vs) b
    else mkFieldTypeAux (v :: vs) s' b f
| e, f => do
  f vs
    (instantiateBVar vs e)

@[inline]
def mkFieldType :
  Name → Expr →
  (f : List Expr → Expr → m α) →
  m α :=
mkFieldTypeAux []

variable [MonadEnv m]

@[inline]
def withFieldTypeAux (s field : Name)
    (f : List Expr → Expr → m α) :
  OptionT m α := do
let env ← getEnv
let s' ← liftOption <| findField? env s field
let info ← liftOption <| getFieldInfo? env s' field
let d ← liftOption <| env.find? info.projFn
let t := d.type
liftM <| mkFieldType s' t f

variable [MonadError m]

@[specialize]
def withFieldType (s field : Name)
    (f : List Expr → Expr → m α) :
    m α := do
let some a ← withFieldTypeAux s field f |>.run
    | throwError "cannot infer field type of {s}.{field}"
return a

def typeOfField (s field : Name) :
    m (List Expr × Expr) := do
withFieldType s field λ vs t => do
  return (vs, t)

def typeOfField' (s field : Name) : MetaM Expr := do
let (_,t) ← typeOfField s field
return t

end Monad

def getFieldInfo' (s field : Name) : OptionT MetaM StructureFieldInfo := do
let env ← getEnv
let s' ← liftOption <| findField? env s field
liftOption <| getFieldInfo? env s' field

def getFieldInfo! (s field : Name) : MetaM StructureFieldInfo := do
let some a ← getFieldInfo' s field |>.run
    | throwError "cannot find field info for {s}.{field}"
return a

def addDef (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
let t ← instantiateMVars t
let d ← instantiateMVars d
addAndCompile
  <| Declaration.defnDecl
  <| DefinitionVal.mk
    (ConstantVal.mk n us t) d
    (ReducibilityHints.regular 10)
    DefinitionSafety.safe
return n

def addInst (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
let t ← instantiateMVars t
let d ← instantiateMVars d
addAndCompile
  <| Declaration.defnDecl
  <| DefinitionVal.mk
    (ConstantVal.mk n us t) d
    (ReducibilityHints.regular 10)
    DefinitionSafety.safe
addInstance n AttributeKind.global (eval_prio default)
return n

def addConst (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
let t ← instantiateMVars t
let d ← instantiateMVars d
addAndCompile
  <| Declaration.opaqueDecl
  <| OpaqueVal.mk
    (ConstantVal.mk n us t) d false
return n

def addThm (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
let t ← instantiateMVars t
let d ← instantiateMVars d
addDecl
  <| Declaration.thmDecl
  <| TheoremVal.mk
    (ConstantVal.mk n us t) d
return n

def addInductive (levels : List Name) (nparams : Nat)
  (decls : List InductiveType) : MetaM Unit := do
addDecl <| Declaration.inductDecl levels nparams decls false
for t in decls do
  let n := t.name
  mkRecOn n
  mkCasesOn n
  Lean.mkNoConfusion n
  mkBelow n
  mkIBelow n
for t in decls do
  let n := t.name
  mkBRecOn n
  mkBInductionOn n

def Simp.Result.proof (r : Simp.Result) : MetaM Expr :=
match r.proof? with
| none => mkAppOptM ``rfl #[r.expr]
| some p => pure p

def applyc (g : MVarId) (n : Name) : MetaM (List MVarId) := do
apply g (← mkConstWithFreshMVarLevels n)

end Lean.Meta

namespace Lean.Elab.Command

elab "#quiet " "check " t:term : command =>
  discard <| withoutModifyingEnv <|
    runTermElabM (some `_check) <| λ _ => Term.elabTerm t none

end Lean.Elab.Command
