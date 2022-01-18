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
