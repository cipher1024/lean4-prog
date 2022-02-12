import Lean.Elab.PreDefinition
import Lib.Tactic

namespace Lean.Meta
open Lean Lean.Elab

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
  let d ← instantiateBVar vs d
  Lean.Meta.withLocalDecl n data.binderInfo d λ v => do
    -- let v' := instantiateBVar vs v
    if d.isConstOf s'
    then f (v :: vs)
          <| instantiateBVar (v :: vs) b
    else mkFieldTypeAux (v :: vs) s' b f
| e, f => do
  f vs
    (← instantiateBVar vs e)

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
let s' ← OptionT.mk <| findField? env s field
let info ← OptionT.mk <| getFieldInfo? env s' field
let d ← OptionT.mk <| env.find? info.projFn
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
let s' ← OptionT.mk <| findField? env s field
OptionT.mk <| getFieldInfo? env s' field

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
n

def addConst (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
let t ← instantiateMVars t
let d ← instantiateMVars d
addAndCompile
  <| Declaration.opaqueDecl
  <| OpaqueVal.mk
    (ConstantVal.mk n us t) d false
n

def addThm (us : List Name) (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
let t ← instantiateMVars t
let d ← instantiateMVars d
addDecl
  <| Declaration.thmDecl
  <| TheoremVal.mk
    (ConstantVal.mk n us t) d
n

def Simp.Result.proof (r : Simp.Result) : MetaM Expr :=
match r.proof? with
| none => mkAppOptM ``rfl #[r.expr]
| some p => pure p

end Lean.Meta
