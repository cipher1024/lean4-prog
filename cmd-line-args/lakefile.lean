import Lake
open Lake DSL

def roots := #[`CLI]

package cli {
  srcDir := "."
  -- libDir := "CLI"
  libRoots := roots
  libGlobs := roots.map Glob.submodules
  -- add configuration options here
}
