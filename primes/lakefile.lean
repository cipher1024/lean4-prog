import Lake
open Lake DSL

package primes {
  -- add configuration options here
  dependencies := #[
      { name := `lib,
        src := Source.path "../lib" } ]
}
