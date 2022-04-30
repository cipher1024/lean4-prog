import Lake
open Lake DSL

def roots := #[`CLI]

package cli {
  srcDir := "."
  -- libDir := "CLI"
  libRoots := roots
  libGlobs := roots.map Glob.submodules
  -- add configuration options here
}


def fail (msg : String) : ScriptM UInt32 := do
  println!"error: {msg}"
  return 1

script deps (xs : List String) := do
let target :: suff :: [] := xs
  | fail "usage: deps TARGET SUFFIX"
let mut result := target ++ ":"
for dep in cli.dependencies do
  match dep.src with
  | .path p =>
    result := result ++ " " ++ p.toString ++ suff
  | .git _ _ => pure ()
IO.println result
return 0
