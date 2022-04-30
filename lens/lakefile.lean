import Lake
open Lake DSL

package lens (dir) (args) {
  defaultFacet := PackageFacet.staticLib
  libRoots :=  #[`Lens] ++
    if args = ["--test"]
      then #[`Test.Lens]
      else #[]
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
for dep in lens "." [] |>.dependencies do
  match dep.src with
  | .path p =>
    result := result ++ " " ++ p.toString ++ suff
  | .git _ _ => pure ()
IO.println result
return 0
