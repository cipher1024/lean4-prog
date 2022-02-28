
structure LockedType {T : Sort u} (T' : Sort u) (x : T) where
  val : T'
  type_eq : T = T'
  val_eqv : HEq val x

infix:50 " ~= " => HEq

theorem Eq.toHEq {α} {x y : α} (h : x = y) : x ~= y :=
by cases h; constructor

theorem HEq.toEq {α} {x y : α} (h : x ~= y) : x = y :=
by cases h; rfl

namespace Transport

class EqvTypes (T T' : Sort u) : Prop where
  rfl : T = T'

class EqvTerm {α α' : Sort u} [EqvTypes α α'] (x : α) (y : α') : Prop where
  rfl : x ~= y

  -- transport : T → T'
  -- transport_eq x : HEq (transport x) x

@[defaultInstance 100] /- low prio -/
instance(priority := low) : EqvTypes T T where
  rfl := rfl
  -- transport := id
  -- transport_eq x := HEq.rfl
-- #check Lean.Meta.PrioritySet
-- #fullname low
-- #find prefix Priority
-- #check Priority.low

@[instance]
def EqvTypes_arrow {α α' : Sort u} {β β' : Sort v}
    [EqvTypes α α'] [EqvTypes β β'] :
         EqvTypes (α → β) (α' → β') where
  rfl := by rw [@EqvTypes.rfl α α', @EqvTypes.rfl β β']

@[instance]
def EqvTypes_forall {α α'} (h' : EqvTypes.{v} α α')
  {β : α → Sort u}
  {β' : α' → Sort u}
  (h : ∀ (x : α) (y : α'), EqvTerm x y → EqvTypes (β x) (β' y)) :
  EqvTypes (∀ x, β x) (∀ x, β' x) where
    rfl := by
      have := h'.rfl; subst this
      have h₀ : ∀ x, β x = β' x :=
        λ x => h x x ⟨ HEq.rfl ⟩ |>.rfl
      have h₁ : β = β' := funext h₀
      rw  [h₁]

def EqvTerm_app {α α'} {β β'} (f : α → β) (g : α' → β') x y
    (h₀ : EqvTypes α α')
    (h₁ : EqvTypes β β')
    (h₂ : EqvTerm f g)
    (h₃ : EqvTerm x y) :
  EqvTerm (f x) (g y) where
    rfl := by
      have := h₀.rfl; subst this
      have := h₁.rfl; subst this
      have := HEq.toEq h₂.rfl; subst this
      have := HEq.toEq h₃.rfl; subst this
      constructor

def EqvTypes_of_EqvTerm {α α'} (h : EqvTerm α α') : EqvTypes α α' where
  rfl := by
    have := h.rfl; cases this
    constructor

macro "prove_transport" : tactic =>
  `(tactic|
    solve
    | repeat
        first
        | intros _
        | assumption
        | apply EqvTypes_arrow
        | apply EqvTypes_forall
        | apply EqvTerm_app
        | apply EqvTypes_of_EqvTerm
        | exact inferInstance )

instance (x : α) : EqvTerm x x where
  rfl := HEq.rfl

def transport α α' [EqvTypes α' α] (x : α) : α' :=
cast EqvTypes.rfl.symm x

def transport_eq α α' [EqvTypes α' α] (x : α) :
  HEq (transport α α' x) x := by
have h := @EqvTypes.rfl α' α _
subst h
constructor

def mkLockedType (α) {α'} (x : α')
    -- (h : EqvTypes α' α := by prove_transport) :
    (h : EqvTypes α α' := by prove_transport) :
    LockedType α x where
  val := transport _ _ x
  type_eq := EqvTypes.rfl.symm
  val_eqv := transport_eq _ _ _

def EqvTerm.ofEq {x y : α} (h : x = y) : EqvTerm x y where
  rfl:= h.toHEq

def EqvTerm.ofHEq {α β} [EqvTypes α β] {x : α} {y : β} (h : x ~= y) :
    EqvTerm x y where
  rfl:= h

end Transport
