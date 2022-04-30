import Lake
open Lake DSL


def roots (args : List String) : Array <| Lean.Name × Glob :=
#[ (`ConcreteSemantics, Glob.submodules `ConcreteSemantics) ] ++
if args = ["--test"]
  then #[ (`Test, Glob.submodules `Test) ]
  else #[]

package ConcreteSemantics (dir) (args) {
  defaultFacet := PackageFacet.bin
  libGlobs := roots args |>.map (·.snd)
  libRoots := roots args |>.map (·.fst)
  dependencies :=
    #[ { name := `lib,
         src := Source.path "../lib" }  ]
}


def fail (msg : String) : ScriptM UInt32 := do
  println!"error: {msg}"
  return 1

script deps (xs : List String) := do
let target :: suff :: [] := xs
  | fail "usage: deps TARGET SUFFIX"
let mut result := target ++ ":"
for dep in ConcreteSemantics "." [] |>.dependencies do
  match dep.src with
  | .path p =>
    result := result ++ " " ++ p.toString ++ suff
  | .git _ _ => pure ()
IO.println result
return 0
