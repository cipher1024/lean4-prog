import Lake
open Lake DSL

def roots (args : List String) : Array <| Lean.Name × Glob :=
#[ (`Lib, Glob.submodules `Lib) ] ++
if args = ["--test"]
  then #[ (`Test, Glob.submodules `Test) ]
  else #[]

package lib (dir) (args) {
  defaultFacet :=
    if args = ["--test"]
      then PackageFacet.oleans
      else PackageFacet.staticLib
  libGlobs := roots args |>.map (·.snd)
  libRoots := roots args |>.map (·.fst)
}


def fail (msg : String) : ScriptM UInt32 := do
  println!"error: {msg}"
  return 1

script deps (xs : List String) := do
let target :: suff :: [] := xs
  | fail "usage: deps TARGET SUFFIX"
let mut result := target ++ ":"
for dep in lib "." [] |>.dependencies do
  match dep.src with
  | .path p =>
    result := result ++ " " ++ p.toString ++ suff
  | .git _ _ => pure ()
IO.println result
return 0
