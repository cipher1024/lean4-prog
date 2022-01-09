import Lake
open Lake DSL

package lean_tools {
  -- binRoot := "."
  -- defaultFacet := PackageFacet.oleans
  dependencies :=
    #[ { name := `lake,
         src := Source.git
           "https://github.com/leanprover/lake"
           "90e4ae7d51a9c0ecffab9057ad9a2bbfba7ed2d6" } ]
}
