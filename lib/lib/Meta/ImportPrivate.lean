
import Lib.Meta.DeclGraph

import Lean.Elab.BuiltinCommand

namespace Lean.Elab.Command
open Name

syntax "import_private " ident : command

def isPrivateDeclNamed : Name → Name → Bool
| str p s _, str p' s' _ =>
  s == s' && isPrivateDeclNamed p p'
| str p s _, _ => False
| num p s _, anonymous => Lean.isPrivateName p
| num p s _, _ => False
| anonymous, _ => False

initialize registerTraceClass `importPrivate

elab_rules : command
| `(import_private $id:ident) => do
  let env ← getEnv
  let id := id.getId
  let ls := env.constants.fold
      (λ l n c =>
        if isPrivateDeclNamed n id
          then  n :: l
          else l ) []
  let str _ s _ := id
    | throwError "invalid name: {id}"
  match ls with
  | [] => throwError "no matches for {id}"
  | [decl] =>
    trace[importPrivate]"found: {decl}"
    let id := (← getCurrNamespace) ++ id.getString!
    trace[importPrivate]"creating private synonym: {(id)}"
    let s    := mkIdent s
    let decl := mkIdent decl
    elabCommand (← `(private def $s:ident := $decl:ident))
  | ns =>
    throwError "too many matches: {ns}"

end Lean.Elab.Command
