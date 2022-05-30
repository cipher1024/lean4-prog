import Lake
open Lake DSL

-- @[script]

package sat (dir) (args) {
  -- add configuration options here
  defaultFacet := PackageFacet.staticLib,
  dependencies := #[
      { name := `lib
        src :=  Source.path "lib"
        args := args },
      { name := `lens
        src :=  Source.path "lens"
        args := args },
      { name := `primes
        src :=  Source.path "primes"
        args := args },
      { name := `cli
        src :=  Source.path "cmd-line-args"
        args := args },
      { name := `advent
        src :=  Source.path "advent"
        args := args },
      { name := `ConcreteSemantics
        src :=  Source.path "concrete-semantics"
        args := args },
      { name := `lean_tools
        src :=  Source.path "lean-tools"
        args := args } ] }

-- def getLocalTarget (dep : Dependency) : Option String :=
-- match dep.src with
-- | .path h =>
--   if h.parent == some ⟨".."⟩
--     then h.fileName
--     else none
-- | _ => none

-- script local_decls (dir : String) (ls : List String) := do
--   println!"hello foo"
--   let s := sat dir ls |>.dependencies.filterMap getLocalTarget
--   println!"deps: {s}"
--   return 0
