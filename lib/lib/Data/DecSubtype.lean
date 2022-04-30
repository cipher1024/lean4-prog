
structure DecSubtype {T : Type u} (p : T → Bool) where
mkImpl ::
  val : T
  property : p val = true

namespace DecSubtype

variable {p : T → Bool}

def mk (x : T) (h : p x = true := by rfl) : DecSubtype p :=
⟨x,h⟩

def test (t : T) : Option (DecSubtype p) :=
if h : p t = true then
  some ⟨t, h⟩
else none

def dtest (t : T) : DecSubtype p ⊕ PLift (p t = false) :=
if h : p t = true then
  Sum.inl ⟨t, h⟩
else Sum.inr ⟨ Bool.not_eq_true _ |>.mp h ⟩

end DecSubtype
