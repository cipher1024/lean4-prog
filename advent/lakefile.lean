import Lake
open Lake DSL

package advent {
  defaultFacet := PackageFacet.staticLib
  dependencies :=
    #[ { name := `lib, src := Source.path "../lib" } ]
}
