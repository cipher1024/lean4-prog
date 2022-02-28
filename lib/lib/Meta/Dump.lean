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
def printVarsAux (acc : Format) :
  List (String × m Format) → m Unit
| [] => IO.println acc
| (x, y) :: [] => do
  let y ← y
  let acc := acc ++ x ++ y
  IO.println acc
| (x, y) :: xs => do
  let y ← y
  printVarsAux (acc ++ x ++ y ++ format "\n") xs

@[inline]
def printVars [MonadLiftT IO m] [Monad m] :
  List (String × m Format) → m Unit :=
printVarsAux ""

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

def dumpListMonadic (ls : List Syntax) : TermElabM Expr := do
  let out ← ls.mapM (λ x => do
    return toString (← Lean.PrettyPrinter.ppTerm x))
  let len := out.map String.length |>.maximum? |>.get!
  let out := out.map <| (padding len . ++ " = ")
  let lines ← out.zipWithM ls λ x y =>
    `(($(Syntax.mkStrLit x), Std.ToFormatM.formatM $y))
  let lines ← mkListLit lines
  Lean.Elab.Term.elabTerm
    (← ``(printVars $lines))
    none

elab "dump_list!" "[" t:(term,*) "]" : term =>
  dumpList t.getSepArgs.toList

elab "print_vars!" "[" t:(term,*) "]" : term => do
  dumpListMonadic t.getSepArgs.toList

elab "dump!" t:term : term =>
  dumpList [t]

end Lean.Elab.Tactic
