-- TODO:
-- * Derive handler
-- * test
-- * cleanup code
-- * add argument type to usage string

import Lean.Elab.AuxDef
import Lean.Elab.BindersUtil
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Elab.MacroArgUtil
import Lean.Elab.Quotation.Precheck
import Lean.Elab.Term

import Lean.Parser.Term
import Lean.PrettyPrinter.Delaborator.Basic

import Lean.Parser.Term
import Lean.Meta.Closure
import Lean.Meta.Check
import Lean.Elab.Command
import Lean.Elab.DefView
import Lean.Elab.PreDefinition
import Lean.Elab.DeclarationRange

import Std.Data.HashMap

import CLI.Format

open Lean Lean.Meta

class CLIArg (α : Type u) where
  typeName : String
  parse : String → Option α

def parseArg (α) [CLIArg α] : String → Option α :=
CLIArg.parse

instance : CLIArg String where
  typeName := "STRING"
  parse := some

instance : CLIArg Nat where
  typeName := "NAT"
  parse := String.toNat?

inductive StreamReader (α : Type u) (β : Type v) where
  | read (f : α → StreamReader α β) : StreamReader α β
  | pure : β → StreamReader α β
  | error : String → StreamReader α β

class CLIArgRecord (α : Type u) where
  init : α
  parse : String → α → Option (StreamReader String α)
  usageString : String

@[simp]
theorem measure_foo (f : α → Nat) :
  (measure f).1 x y ↔ f x < f y := Iff.rfl

@[simp]
theorem dec_double (x k : Nat) :
  x < x + k ↔ 0 < k := sorry

@[simp]
theorem dec_double''' (i j : Nat) :
  x + i.succ + j = x + i + j.succ := sorry

@[simp]
theorem dec_double'' (i j : Nat) :
  x + i < x + j ↔ i < j := sorry

@[simp]
theorem dec_double' (x y : Nat) :
  x * y.succ = x*y + x := sorry

mutual

variable (α : Type) [CLIArgRecord α]
variable (interspersedArgs : Bool)

@[inline]
def parseArgsFeed (acc : List String)
    (args : List String)
     : StreamReader String α →
       Except String (α × Array String)
| StreamReader.pure x' => parseArgsAux acc x' args
| StreamReader.error msg => Except.error msg
| StreamReader.read f =>
  match args with
  | [] => Except.error "expecting more arguments"
  | y::ys => parseArgsFeed acc ys (f y)

@[inline]
def parseArgsAux (acc : List String) (x : α)
     : List String →
  Except String (α × Array String)
| [] => pure (x, acc.reverse.toArray)
| y :: ys =>
  match CLIArgRecord.parse y x with
  | none =>
    if interspersedArgs
    then parseArgsAux (y :: acc) x ys
    else pure (x, (acc.reverse ++ y :: ys).toArray)
  | some r =>
    parseArgsFeed acc ys r

end

termination_by
  parseArgsFeed x _ => (2 * x.length) + 1
  parseArgsAux x => 2 * x.length
decreasing_by simp [InvImage, WellFoundedRelation.rel, sizeOf]


@[specialize]
def parseArgs (α : Type) [CLIArgRecord α]
    (args : Array String) (interspersedArgs : Bool) :
  Except String (α × Array String) :=
parseArgsAux α
  interspersedArgs [] CLIArgRecord.init args.toList

def LeftOvers (α : Type) (allowed : Bool) :=
  cond allowed (α × Array String) α

instance [Repr α] {allowed} : Repr (LeftOvers α allowed) :=
match allowed with
| true => inferInstanceAs (Repr (α × Array String))
| false => inferInstanceAs (Repr α)

def processCmdLine  (α : Type) [CLIArgRecord α]
    (args : Array String)
    (interspersedArgs := false)
    (allowLeftOvers := false) :
  IO (LeftOvers α allowLeftOvers) := do
let (r, ar) ←
  match parseArgs α args interspersedArgs with
  | Except.error msg =>
    throw <| IO.userError
      <| s!"{msg}\n\n{CLIArgRecord.usageString α}"
  | Except.ok (r, ar) => pure (r, ar)
match allowLeftOvers with
| true => return (r, ar)
| false =>
  if ar.isEmpty then return r
  else throw
      <| IO.userError
      <| s!"Excess arguments: {ar}\n\n{CLIArgRecord.usageString α}"

abbrev CmdLineFlag (short : String) (long : Option String) (descr : String) := Bool

abbrev CmdLineOpt (short : String) (long : Option String) (t : Type) [CLIArg t]
  (descr : String) := Option t

structure Flags where
  traceCmd :
    CmdLineFlag "-c" (some "--cmd")
    "tracing: print command"
  traceSubst :
    CmdLineFlag "-s" none
    "tracing: print module renaming"
  traceRoot :
    CmdLineFlag "-r" none
    "tracing: print command"
  optValue :
    CmdLineOpt "-t" none Nat
    "tracing: test option parsing"
  dryRun :
    CmdLineFlag "-d" none
    "dry run: calculate parameters but perform no action"
  forward : Array String := #[]
                           -- array of -f, -i, -n, -v, -k
  deriving Repr, Inhabited

namespace CLI
open Lean

def instantiateBVarAux (i : Nat) (vs : List Expr) (e : Expr) :
  Expr :=
if e.looseBVarRange > 0 then e else
  match e with
  | Expr.forallE n d b data =>
    Expr.forallE n
      (instantiateBVarAux i vs d)
      (instantiateBVarAux (i+1) vs b) data
  | Expr.lam n d b data     =>
    Expr.lam n
      (instantiateBVarAux i vs d)
      (instantiateBVarAux (i+1) vs b) data
  | Expr.mdata m e d        =>
    Expr.mdata m (instantiateBVarAux i vs e) d
  | Expr.letE n t v b data  =>
    Expr.letE n
      (instantiateBVarAux i vs t)
      (instantiateBVarAux i vs v)
      (instantiateBVarAux (i+1) vs b) data
  | Expr.app f a data       =>
    Expr.app
      (instantiateBVarAux i vs f)
      (instantiateBVarAux i vs a)
      data
  | Expr.proj r j e data    =>
    Expr.proj r j (instantiateBVarAux i vs e) data
  | e@(Expr.bvar j _)  => vs.getD (j - i) e
  | e                       => e

def instantiateBVar (vs : List Expr) (e : Expr) : Expr :=
instantiateBVarAux 0 vs e

def mkFieldTypeAux (vs : List Expr) (s' : Name) :
  Expr → MetaM (List Expr × Expr)
| Expr.forallE n d b _  =>
  Lean.Meta.withLocalDeclD n d λ v =>
    if d.isConstOf s'
    then return (v :: vs, instantiateBVar (v :: vs) b)
    else mkFieldTypeAux (v :: vs) s' b
| e => return (vs, e)

def mkFieldType : Name → Expr → MetaM (List Expr × Expr) :=
mkFieldTypeAux []

def typeOfField' (s field : Name) : OptionT MetaM Expr := do
let env ← getEnv
let s' ← liftOption <| findField? env s field
let info ← liftOption <| getFieldInfo? env s' field
let d ← liftOption <| env.find? info.projFn
let t := d.type
Prod.snd <$> mkFieldType s' t

def typeOfField (s field : Name) : MetaM Expr := do
let some a ← typeOfField' s field |>.run
    | throwError "cannot infer field type of {s}.{field}"
return a

def getFieldInfo' (s field : Name) : OptionT MetaM StructureFieldInfo := do
let env ← getEnv
let s' ← liftOption <| findField? env s field
liftOption <| getFieldInfo? env s' field

def getFieldInfo! (s field : Name) : MetaM StructureFieldInfo := do
let some a ← getFieldInfo' s field |>.run
    | throwError "cannot find field info for {s}.{field}"
return a

structure FlagDescr where
  field : Name
  projection : Name
  shortOpt : String
  longOpt : Option String
  optType : Option Syntax
  description : String
  deriving Repr, Inhabited

def parseStringLit [Monad m] [MonadError m] (s : Syntax) :
  m String := do
  let some x := Syntax.isStrLit? s
    | throwError "expecting string literal {s}"
  return x

def parseShortOpt [Monad m] [MonadError m]
    (s : Syntax) : m String := do
  let x ← parseStringLit s
  unless ("-".isPrefixOf x ∧ x.length = 2) do
    throwError "invalid short option '{x}'"
  return x

def parseLongOpt [Monad m] [MonadError m] :
  Syntax → m (Option String)
| `(none) => pure none
| `(some $x) => do
  let x ← parseStringLit x
  unless ("--".isPrefixOf x ∧ x.length > 2) do
    throwError "invalid long option '{x}'"
  return some x
| e => throwError "Expecting a literal string: {e}"

open Lean.Elab.Term

def mkFlagDescr (struct field : Name) :
  TermElabM (Option FlagDescr) := do
let t ← typeOfField struct field
let proj := (← getFieldInfo! struct field).projFn
let s ← Lean.PrettyPrinter.delab t
match s with
| `(CmdLineFlag $x $y $descr) =>
  return some {
    field := field,
    projection := proj,
    shortOpt := ← parseShortOpt x,
    longOpt := ← parseLongOpt y,
    optType := none,
    description := ← parseStringLit descr : FlagDescr }
| `(CmdLineOpt $x $y $t $descr) =>
  return some {
    field := field,
    projection := proj,
    shortOpt := ← parseShortOpt x,
    longOpt := ← parseLongOpt y,
    optType := some t,
    description := ← parseStringLit descr : FlagDescr }
| _ => return none

section

open Lean.Meta
open Lean Parser Term Elab Term

def optionParsingFailure (x : String) :
  Option (StreamReader String α) :=
if "-".isPrefixOf x then
  some <| StreamReader.error s!"Invalid option: {x}"
else
  none

def mkOptParser (arg₀ obj : Syntax)
                (flag : FlagDescr) :
    TermElabM Syntax :=
withFreshMacroScope do
  let field := mkIdent flag.field
  let proj := mkIdent flag.projection
  let flagString :=
    match flag.longOpt with
    | some opt =>  opt
    | none =>  flag.shortOpt
  let parsingErrorMsg :=
    s!"Flag {flagString} requires an argument of type "
  let parsingErrorMsg := Syntax.mkStrLit parsingErrorMsg
  let redundantOptMsg :=
    s!"Flag {flagString} should be provided only once"
  let redundantOptMsg := Syntax.mkStrLit redundantOptMsg
  if let some type := flag.optType then
    let successCode ← `(StreamReader.pure
           { $obj with $field:ident := some val } )
    let errorCode ← `(StreamReader.error <|
        $parsingErrorMsg ++ CLIArg.typeName $type)
    let redundantOpt ← `(StreamReader.error <| $redundantOptMsg)
    let br1 ← `(matchAltExpr| | none => $errorCode)
    let br2 ← `(matchAltExpr| | some val => $successCode)
    let brs := #[br1, br2]
    let discr ← `(parseArg $type arg₁)
    let body ← `(match $discr:term with $brs:matchAlt*)
    let parseArg ← `(StreamReader.read λ arg₁ => $body)
    `(some <| if ($proj $obj).isNone
              then $parseArg
              else $redundantOpt )
  else
    `(some <| StreamReader.pure
        { $obj with $field:ident := true } )


end

/--
Generate a function

def MyStruct.parseArg (s : String) (x : MyStruct) : Option MyStruct := ...

Note: this is broken because I don't know how to create
and elaborate a syntax object of the form `{x with foo := 7}`
-/
def mkArgParserAux
  -- [Monad m] [MonadRef m] [MonadQuotation m]
  (type : Name) (arg obj : Syntax) :
  List FlagDescr → TermElabM Syntax
| [] => `(optionParsingFailure $arg)
| flag :: fs => do
  let code ← mkArgParserAux type arg obj fs
  let field := mkIdent flag.field
  let thenBr ← mkOptParser arg obj flag
  let elseBr ←
    if let some longOpt := flag.longOpt then
      `(if $arg = $(Syntax.mkStrLit longOpt)
        then $thenBr
        else $code )
    else pure code
  `(if $arg = $(Syntax.mkStrLit flag.shortOpt)
    then $thenBr
    else $elseBr)

def addDef (n : Name) (t : Expr) (d : Expr) : MetaM Name := do
let t ← instantiateMVars t
let d ← instantiateMVars d
addAndCompile
  <| Declaration.defnDecl
  <| DefinitionVal.mk
    (ConstantVal.mk n [] t) d
    (ReducibilityHints.regular 10)
    DefinitionSafety.safe
return n

def mkArgParser (type : Name)
  (flags : List FlagDescr) : TermElabM Name :=
let n := type.mkStr "parseArg"
withDeclName n do
withFreshMacroScope do
  let arg ← `(arg)
  let obj ← `(obj)
  let b ← mkArgParserAux type arg obj flags
  let type' := mkIdent type
  let t ← Elab.Term.elabTerm
      (← `(String → $type' →
           Option (StreamReader String $type'))) none
  let d ← withDeclName n <| Elab.Term.elabTerm
    (← `(λ ($arg : String)
           ($obj : $type') => $b))
    (some t)
  addDef n t d

open Lean.Parser.Term
open Lean.Elab Term Meta

def mkInitAux (type : Name)
  (flags : List FlagDescr) : TermElabM Syntax := do
let fieldInits := flags.toArray
let fieldInits ← fieldInits.mapM λ fl => do
  let field := mkIdent fl.field
  let val ←
    if fl.optType.isSome then `(none)
    else `(false)
  `(structInstField| $field:ident := $val )
`({ $[$fieldInits,]* : $(mkIdent type) })

def mkInitialization (type : Name)
  (flags : List FlagDescr) : TermElabM Name :=
let n := type.mkStr "init"
withDeclName n do
withFreshMacroScope do
  let t := Lean.mkConst type
  let d ← withDeclName n <| Elab.Term.elabTerm
    (← mkInitAux type flags)
    (some t)
  addDef n t d

-- #check ConstantInfo
open Std

section UsageString

open Document.Table
open Document.Paragraph

def mkUsageString' (flags : List FlagDescr) : String :=
let t := flags.map λ fl =>
  (#[rightAlign fl.shortOpt,
     leftAlign <| fl.longOpt.getD ""],
   fl.description)
let descrWidth := 60
let t := t.map <| Prod.map id <| wrapParagraph descrWidth
let empty := leftAlign ""
let t := t.bind λ
  | (a,[]) => [a.push <| empty]
  | (a,l::ls) =>
    a.push (leftAlign l) ::
    ls.map (#[empty,empty].push ∘ leftAlign)
let t :=
  #[leftAlign "Flags", empty, leftAlign "Description"] ::
  t
renderTable t

def mkUsageString (struct : Name)
    (flags : List FlagDescr) : MetaM Name := do
let usage := mkUsageString' flags
let n := struct.mkStr "usageString"
let t ← mkConstWithLevelParams ``String
let e := mkStrLit usage
println!"name: {n}"
addDef n t e

end UsageString

def elabCLIArgRecordInst (struct : Name)
    (init parser usage : Syntax) :
  TermElabM (Expr × Expr) := do
let t ← elabTerm (← `(CLIArgRecord $(mkIdent struct))) none
let e ← elabTerm
  (← `( { init := $init,
          parse := $parser,
          usageString := $usage } ))
  (some t)
return (t, e)


def mkCLIArgRecordInst' (struct : Name)
    (flags : List FlagDescr) : TermElabM Name := do
let usage := mkIdent (← mkUsageString struct flags)
let parser := mkIdent (← mkArgParser struct flags)
let init := mkIdent (← mkInitialization struct flags)
let (t, e) ← elabCLIArgRecordInst struct init parser usage
let n := struct.mkStr "instCLIArgRecord"
addDef n t e

def mkCLIArgRecordInst (struct : Name) : TermElabM Name :=
withDeclName struct do
let env ← getEnv
let fields := getStructureFieldsFlattened env struct
let flags ← fields.toList.filterMapM <| mkFlagDescr struct
let inst ← mkCLIArgRecordInst' struct flags
addInstance inst AttributeKind.«global» 0
return inst

def test : MetaM Unit := do
let env ← getEnv
let struct := ``Flags
IO.println <| (← mkCLIArgRecordInst struct |>.run')
IO.println <| repr struct

-- #eval mkCLIArgRecordInst ``Flags
#eval test

-- #check Flags.usageString
-- #check Flags.parseArg

-- instance : CLIArgRecord Flags where
--   init := {}
--   parse := Flags.parseArg
--   usageString :=  Flags.usageString
namespace Derive
open Lean.Elab.Command

def mkCLIArgRecordInstanceHandler' : Array Name → CommandElabM Bool
| #[t] => do
  -- println! "foo"
  -- liftTermElabM none <| discard <| mkCLIArgRecordInst t
  return true
| _ => do
  -- throwError "Mutually inductive types not supported"
  return false


def mkCLIArgRecordInstanceHandler : Array Name → CommandElabM Bool
| #[t] => do
  return true
| _ => do
  return true

builtin_initialize
  Lean.Elab.registerBuiltinDerivingHandler `CLIArgRecord
    mkCLIArgRecordInstanceHandler

-- structure Foo where
--   field1 := false
--   deriving CLIArgRecord

end Derive

#eval parseArgs Flags #["-d", "a", "-r", "-t", "3", "z"] false

#eval processCmdLine Flags #["-d", "a", "-r", "-t", "3"] true true
-- #eval parseArgsUnordered Flags #["--cmd", "a", "-r"]

end CLI
