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
