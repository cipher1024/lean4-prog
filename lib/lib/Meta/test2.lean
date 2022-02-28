
import Lib.Meta.Opaque

namespace Bar
namespace Foo

-- set_option trace.opaque.decls true
opaque def Term := Unit
end Foo

#check Foo.Term._locked
-- #check _impl.Term
#check Foo.Term._impl.Term

namespace Foo
-- #check Term.instEqvTerm
-- local notation "Term" => Term._def
-- section A
opaque namespace Term

set_option trace.opaque true
open Lean
-- @[transport foo]
def fvar (x : Name) : Term :=
()

def rec {motive : Term → Sort u} (f : ∀ n, motive (fvar n)) : ∀ t, motive t :=
sorry

-- #check foo
#print Foo.Term.fvar._locked
#check Foo.Term.fvar
-- end Term._impl

end Term
#print Foo.Term._impl.fvar
end Foo
