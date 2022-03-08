
import Lib.Meta.Opaque

namespace Bar
namespace Foo

opaque def Term := Unit

end Foo

namespace Foo

opaque namespace Term

open Lean

def fvar (x : Name) : Term :=
()

open Lean.Parser.Transport

def rec {motive : Term → Sort u} (f : ∀ n, motive (fvar n)) : ∀ t, motive t :=
sorry

theorem foo (n) : fvar n = fvar n := sorry

#check @Foo.Term.rec

end Term

#print Term.foo

end Foo
