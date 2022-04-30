
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Elab.Declaration
import Lib.Meta.DeclGraph


namespace Lean.Elab.Command
namespace About

abbrev AboutM := StateT MessageData TermElabM

def log (m : MessageData) : AboutM Unit := do
let ctx ← readThe Core.Context
let m := MessageData.withNamingContext {
    currNamespace := ctx.currNamespace
    openDecls := ctx.openDecls } m
modify (. ++ m ++ m!"\n")

def runM (cmd : AboutM α) : CommandElabM α := do
let (r, msgs) ← liftTermElabM none <| StateT.run cmd ""
logInfo (toMessageData msgs)
return r

open Lean.Meta

section forallTelescopeUntil

register_option about.print_instance_arguments : Bool :=
  { defValue := false
    descr := "enable printing arguments of instances" }

private partial def forallTelescopeUntilAux
    (untilFVar : LocalDecl → Bool → Bool)
    (type              : Expr)
    (k                 : Array Expr → Expr → MetaM α) : MetaM α := do
  let rec process (fvars : Array Expr) (j : Nat) (type : Expr) : MetaM α := do
    match type with
    | Expr.forallE n d b c =>
      withLocalDecl n c.binderInfo d λ v => do
      let lctx ← getLCtx
      let ldecl := lctx.getFVar! v
      if !untilFVar ldecl (b.hasLooseBVar 0) then
        let d     := d.instantiateRevRange j fvars.size fvars
        let fvarId ← mkFreshFVarId
        let lctx  := lctx.mkLocalDecl fvarId n d c.binderInfo
        let fvar  := mkFVar fvarId
        let fvars := fvars.push fvar
        withReader (fun ctx => { ctx with lctx := lctx }) do
          process fvars j b
      else
        let type := type.instantiateRevRange j fvars.size fvars;
        withReader (fun ctx => { ctx with lctx := lctx }) do
            k fvars type
    | _ =>
      let type := type.instantiateRevRange j fvars.size fvars;
      k fvars type
  process #[] 0 type

variable [MonadControlT MetaM n] [Monad n]

def forallTelescopeUntil
    (untilFVar : LocalDecl → Bool → Bool)
    (type              : Expr)
    (k                 : Array Expr → Expr → n α) : n α := do
map2MetaM (forallTelescopeUntilAux untilFVar type) k

end forallTelescopeUntil

deriving instance DecidableEq for BinderInfo

def printParams (vs : Array Expr) (indent : Nat) : AboutM Unit := do
if vs.size > 0 then
  let margin := indent.fold (init := "") λ _ acc => acc ++ " "
  log m!"{margin}with parameters"
  -- println!"{margin}with parameters"
  let lctx ← getLCtx
  for v in vs do
    let ldecl := lctx.getFVar! v
    if ldecl.binderInfo == BinderInfo.instImplicit then
      log m!"{margin}  [{← Lean.Meta.ppExpr ldecl.type}]"
    else
      log m!"{margin}  {ldecl.userName} : {← Lean.Meta.ppExpr ldecl.type}"

def printParents (n : Name) (vs : Array Expr) : AboutM Unit := do
  let c ← mkConstWithLevelParams n
  let ls := c.constLevels!
  let c := mkAppN c vs
  withLocalDeclD `_ c λ x => do
    let env ← getEnv
    let fieldNames := getStructureFields env n;
    let subobjs := fieldNames.foldl (init := #[])
      fun acc fieldName =>
      flip Option.getD acc <| OptionT.run (m := Id) <| do
        let parentStructName ← isSubobjectField? env n fieldName
        let proj ← getFieldInfo? env n fieldName
        return acc.push proj.projFn
    let args := vs.push x
    let parents ← subobjs.mapM λ par => do
        inferType (mkAppN (mkConst par ls) args)
    if parents.size > 0 then
      let parents := (← liftMetaM <| parents.mapM Meta.ppExpr).toList
      let parentLine := Format.joinSep parents ", "
      log m!"extends {parentLine}"

def aboutStructProj (n : Name) : AboutM Unit := do
let c ← mkConstWithLevelParams n
let ls := c.constLevels!
let t ← inferType c
forallTelescope t λ vs t =>
let c := mkAppN c vs
withLocalDeclD `x c λ x => do
  let env ← getEnv
  log m!"structure {← Meta.ppExpr c}"
  printParents n vs
  printParams vs 0
  let ctor := getStructureCtor env n
  log m!"{ctor.name.replacePrefix n Name.anonymous} ::"
  let fields := getStructureFields env n
  let args := vs.push x
  for field in fields do
    if isSubobjectField? env n field |>.isNone then
      let some proj := getFieldInfo? env n field
        | throwError "{field} is not a field of {n}"
      -- let some x := env.getProjectionFnInfo? field
      let fn := mkConst proj.projFn ls
      let t ← inferType (mkAppN fn args)
      log m!"  {field} : {← Meta.ppExpr t}"
  return ()

def aboutCtors (n : Name) : AboutM Unit := do
let some (.inductInfo induct) :=
    (← getEnv).find? n
  | return ()
let c ← mkConstWithLevelParams n
let ls := c.constLevels!
let t ← inferType c
forallBoundedTelescope t (some induct.numParams) λ vs t => do
  let c := mkAppN c vs
  let t ← inferType c
  log m!"inductive {← Meta.ppExpr c} : {← Meta.ppExpr t}"
  for ctor in induct.ctors do
    let ctor' := mkAppN (mkConst ctor ls) vs
    let t ← inferType ctor'
    forallTelescopeUntil (λ _ => not) t λ vs t => do
      log m!"| {ctor.replacePrefix n Name.anonymous} : {← Meta.ppExpr t}"
      printParams vs 4
  printParams vs 0

def aboutInstances (n : Name) : AboutM Unit := do
log m!""
let env ← getEnv
let insts := globalInstanceExtension.getState env |>.toList
for (inst, _) in insts do
    let c ← mkConstWithLevelParams inst
    let t ← inferType c
    forallTelescope t λ vs t => do
      if t.foldConsts false λ c b => b || c == n then
          log m!"{inst} :\n  {← Meta.ppExpr t}"
          let b ← getBoolOption `about.print_instance_arguments
          if b then
            printParams vs 0
          log m!""

def aboutTypeSignature (n : Name) : AboutM Unit := do
let c ← mkConstWithLevelParams n
let t ← inferType c
forallTelescopeUntil
  (λ l _ => l.binderInfo = BinderInfo.default) t λ vs t => do
  let c := mkAppN c vs
  log m!"{← Lean.Meta.ppExpr  c} : {← Lean.Meta.ppExpr t}"
  printParams vs 2

def cmdAbout (n : Name) : CommandElabM Unit :=
runM do
  let env ← getEnv
  let some c := env.find? n
    | throwError "{n} is not a declaration"
  if isStructure env n then
    aboutStructProj n
  else if c.isInductive then
    aboutCtors n
  else
    aboutTypeSignature n
  aboutInstances n

syntax "#about " ident : command

elab_rules : command
| `(#about%$tk $id:ident) => do
  withRef tk <| do
  addCompletionInfo <| CompletionInfo.id id id.getId (danglingDot := false) {} none
  cmdAbout (← resolveGlobalConstNoOverloadWithInfo id)

end About
end Lean.Elab.Command
