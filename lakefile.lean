import Lake
open Lake DSL

package sat {
  -- add configuration options here
  defaultFacet := PackageFacet.staticLib,
  dependencies := #[{
      name := `lib
      src :=  Source.path "lib" } ]
  -- dependencies := #[{
  --     name := `mathlib
  --   src := Source.git "https://github.com/leanprover-community/mathlib4.git" "master"

  -- }]
}
