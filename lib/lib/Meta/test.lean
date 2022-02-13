import Lib.Meta.Opaque
import Lib.Meta.DeclGraph
import Lib.Meta.ImportPrivate
import Lib.Meta.Dump

import Lean.Elab.BuiltinCommand

opaque def append : List α → List α → List α
| [], ys => ys
| x :: xs, ys => x :: append xs ys

open Lean.Parser
open Lean.Elab.Command

set_option trace.opaque.decls true

syntax (name := opaqueSection)
   "opaque " "section " ident : command

syntax (name := opaqueSectionEnd)
  "myend " ident : command

import_private Lean.Elab.Command.addNamespace

@[commandElab opaqueSection]
def elabOpaqueSection : CommandElab := λ stx => do
match stx with
| `(opaque section $id:ident) =>
-- λ stx =>
  -- println!"foo"
  addNamespace id.getId
| _ => println!"wtf"
#print Lean.Options
open Lean
#check addDecl
#pred MonadEnv
deriving instance Repr for Lean.OpenDecl
deriving instance Repr for Lean.DataValue
deriving instance Repr for Lean.KVMap
-- #check @StateRefT'.instMonadLiftStateRefT'
#check Core.State
set_option pp.explicit true in
#check inferInstanceAs (MonadState _ CoreM)
#check @instMonadEnv
#check Core.instMonadEnvCoreM
#check @ReaderT.instMonadLiftReaderT
set_option pp.explicit true in
#check inferInstanceAs (MonadEnv MetaM)
-- #check instMonadEnv
instance : Repr Lean.Options :=
inferInstanceAs (Repr Lean.KVMap)
-- deriving instance Repr for NameGenerator
-- deriving instance Repr for EnvironmentHeader
-- deriving instance Repr for Environment
-- deriving instance Repr for MessageLog
-- deriving instance Repr for Elab.InfoState
-- deriving instance Repr for TraceState

-- -- #succ Nat
-- #succ Lean.EnvExtensionState
-- #succ Environment
-- #check EnvExtensionState
-- #fullname Extension
deriving instance Repr for Scope
-- deriving instance Repr for State

@[commandElab opaqueSectionEnd]
def elabOpaqueSectionEnd : CommandElab := λ stx => do
match stx with
| `(myend $id:ident) =>
  let s ← get
  -- println!"id: {id}"
  print_vars![id]
| _ => println!"wtf"


-- elab_rules
-- | `(command| opaque section $id:ident) => `(command| namespace $id)

-- syntax (name := opaqueSection)
--    "opaque " "section " ident
--    (ppLine (! "end ") command)* "end " ident : command

opaque section append

def foo := 3

myend append
