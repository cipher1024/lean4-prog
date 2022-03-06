import Lake
open Lake DSL

package lean_tools {
  -- binRoot := "."
  -- defaultFacet := PackageFacet.oleans
  defaultFacet := PackageFacet.bin
  dependencies :=
    #[ { name := `lake,
         src := Source.git
           "https://github.com/leanprover/lake"
           "9378575b5575f49a185d50130743a190a9be2f82" } ]
}
