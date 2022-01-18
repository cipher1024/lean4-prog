import Lens

structure Foo (α β : Type) where
  x : Nat
  y : α
  z : List (α × β)
  deriving Lenses

variable {α β : Type}

#check (Foo.Lens.x : Lens (Foo α β) Nat)
#check (Foo.Lens.y : Lens (Foo α β) α)
#check (Foo.Lens.z : Lens (Foo α β) (List (α × β)))

structure Bar (α β : Type) where
  foo : Foo α β
  deriving Lenses

namespace Lens
open Foo.Lens Bar.Lens

variable (a : Bar Nat Nat)

def bar : Bar Nat Nat :=
a & foo /. x %~ (. + 3)

#check (Bar.Lens.foo : Lens (Bar α β) (Foo α β))
#check (Bar.Lens.foo /. Foo.Lens.x : Lens (Bar α β) Nat)

def test := bar ⟨ { x := 1, y := 0, z := [] } ⟩

theorem check : test = ⟨ { x := 4, y := 0, z := [] } ⟩ :=
rfl

end Lens
