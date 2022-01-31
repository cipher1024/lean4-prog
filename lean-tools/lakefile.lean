import Lake
open Lake DSL

package lean_tools {
  -- binRoot := "."
  -- defaultFacet := PackageFacet.oleans
  dependencies :=
    #[ { name := `lake,
         src := Source.git
           "https://github.com/leanprover/lake"
           "3cd49e6e180c1837adb495f48016c524032933c8" } ]
}
