import Lean.PrettyPrinter

import Lib.Meta.Format
import Lib.Data.List.Control
import Lib.Data.String.Defs

namespace Lean.Syntax
variable [Monad m]
variable [MonadRef m]
variable [MonadQuotation m]

def mkListLit : List Syntax → m Syntax
| [] => `(List.nil)
| x :: xs => do `(List.cons $x $(← mkListLit xs))

def mkStringLit' (ref : Syntax) (s : String) : Syntax :=
let pos := ref.getHeadInfo
node pos strLitKind #[atom pos s]

def mkStringLit [Monad m] [MonadRef m] (s : String) : m Syntax := do
let pos ← MonadRef.mkInfoFromRefPos
return node pos strLitKind #[atom pos s]

end Lean.Syntax

namespace Lean.Elab.Tactic

open Syntax Lean.Meta

section printVars
variable [MonadLiftT IO m] [Monad m]

@[inline]
def formatVarsAux (acc : Format) :
  List (String × m Format) → m Format
| [] => pure acc
| (x, y) :: [] => do
  let y ← y
  let acc := acc ++ x ++ y
  return acc
| (x, y) :: xs => do
  let y ← y
  formatVarsAux (acc ++ x ++ y ++ format "\n") xs

@[inline]
def formatVars [MonadLiftT IO m] [Monad m] :
  List (String × m Format) → m Format :=
formatVarsAux ""

def printVars [MonadLiftT IO m] [Monad m]
  (vars : List (String × m Format)) : m Unit := do
IO.println (← formatVars vars)

end printVars

open String

def dumpListAux : List Syntax → TermElabM Syntax
| [] => `( "" )
| [x] => pure x
| x :: xs => do
  `( $x ++ "\n" ++ $(← dumpListAux xs) )

def dumpList (ls : List Syntax) : TermElabM Expr := do
  let out ← ls.mapM (λ x => do
    return toString (← Lean.PrettyPrinter.ppTerm x))
  let len := out.map String.length |>.maximum? |>.get!
  let out := out.map <| (padding len . ++ " = ")
  let lines ← out.zipWithM ls λ x y =>
    `($(Syntax.mkStrLit x) ++ toString $y)
  Lean.Elab.Term.elabTerm
    (← dumpListAux lines)
    (some (mkConst ``String))

def formatListMonadic (ls : List Syntax) : TermElabM Syntax := do
  let out ← ls.mapM (λ x => do
    return toString (← Lean.PrettyPrinter.ppTerm x))
  let len := out.map String.length |>.maximum? |>.get!
  let out := out.map <| (padding len . ++ " = ")
  let lines ← out.zipWithM ls λ x y =>
    `(($(Syntax.mkStrLit x), Std.ToFormatM.formatM $y))
  mkListLit lines

open Lean.Elab.Term (elabTerm)

def dumpListMonadic (ls : List Syntax) : TermElabM Expr := do
  let lines ← formatListMonadic ls
  Lean.Elab.Term.elabTerm
    (← ``(printVars $lines))
    none

elab "dump_list!" "[" t:(term,*) "]" : term =>
  dumpList t.getSepArgs.toList

elab "dump_vars!" "[" t:(term,*) "]" : term => do
  let msg ← formatListMonadic t.getSepArgs.toList
  elabTerm (← `(formatVars $msg)) none

elab "print_vars!" "[" t:(term,*) "]" : term => do
  dumpListMonadic t.getSepArgs.toList

elab "dump!" t:term : term =>
  dumpList [t]

elab "trace_vars![" id:ident "]" "[" t:(term,*)  "]" : term => do
  let msg ← formatListMonadic t.getSepArgs.toList
  elabTerm (← `(do
    let cls := $(quote id.getId.eraseMacroScopes)
    if (← Lean.isTracingEnabledFor cls) then

      Lean.addTrace cls <| "\n" ++ (← formatVars $msg)))
    none

end Lean.Elab.Tactic
