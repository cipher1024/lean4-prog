import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.PrettyPrinter.Delaborator.Basic

-- import CLI.Args

-- structure Foo where
--   l1 : CmdLineFlag "-c" "--long" "description" := false
--   deriving CLIArgRecord
open Lean Lean.Elab Lean.Elab.Command

class CLIArgRecord (α : Type)
namespace Lean.Elab.Deriving.CLIArgRecord


def mkCLIArgRecordInstanceHandler : Array Name → CommandElabM Bool
| #[t] => do
  return true
| _ => do
  return true

builtin_initialize do
  IO.FS.writeFile "text.txt" "foo"
  let initializing ← IO.initializing
  IO.FS.writeFile "text2.txt" s!"init: {initializing}"
  registerBuiltinDerivingHandler `CLIArgRecord
    mkCLIArgRecordInstanceHandler

end Lean.Elab.Deriving.CLIArgRecord
