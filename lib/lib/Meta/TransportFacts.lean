
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

structure EqvTypes (T T' : Sort u) : Prop where
  rfl : T = T'

class EqvTerm {α α' : Sort u} (x : α) (y : α') : Prop where
  rfl : x ~= y

def refl : EqvTypes T T where
  rfl := rfl

def EqvTypes_arrow {α α' : Sort u} {β β' : Sort v}
    (h₀ : EqvTypes α α') (h₁ : EqvTypes β β') :
         EqvTypes (α → β) (α' → β') where
  rfl := by rw [h₀.rfl, h₁.rfl]

def EqvTypes_forall' {α}
  {β : α → Sort u}
  {β' : α → Sort u}
  (h : ∀ (x : α), EqvTypes (β x) (β' x)) :
  EqvTypes (∀ x, β x) (∀ x, β' x) where
    rfl := by
      have h₀ : ∀ x, β x = β' x :=
        λ x => h x |>.rfl
      have h₁ : β = β' := funext h₀
      rw  [h₁]

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

def EqvTerm_app' {α α'} {β : α → Type u} {β' : α' → Type u}
    (f : (x : α) → β x) (g : (x : α') → β' x) x y
    (h₀ : EqvTypes α α')
    (h₁ : EqvTerm β β')
    (h₂ : EqvTerm f g)
    (h₃ : EqvTerm x y) :
  EqvTerm (f x) (g y) where
    rfl := by
      have := h₀.rfl; subst this
      have := HEq.toEq h₃.rfl; subst this
      have := HEq.toEq h₁.rfl; subst this
      have := HEq.toEq h₂.rfl; subst this
      constructor

def EqvTypes_of_EqvTerm {α α'} (h : EqvTerm α α') : EqvTypes α α' where
  rfl := by
    have := h.rfl; cases this
    constructor

instance EqvTypes_of_EqvTerm' {α α'} [EqvTerm α α'] : EqvTypes α α' :=
by apply EqvTypes_of_EqvTerm <;> assumption

instance (x : α) : EqvTerm x x where
  rfl := HEq.rfl

def transport α α' (h : EqvTypes α' α) (x : α) : α' :=
cast (EqvTypes.rfl h |>.symm) x

def transport_eq α α' (h : EqvTypes α' α) (x : α) :
  HEq (transport α α' h x) x := by
have h := @EqvTypes.rfl α' α h
subst h
constructor

def mkLockedType (α) {α'} (x : α')
    -- (h : EqvTypes α' α := by prove_transport) :
    (h : EqvTypes α α') :
    LockedType α x where
  val := transport _ _ h x
  type_eq := EqvTypes.rfl h |>.symm
  val_eqv := transport_eq _ _ h _

def EqvTerm.ofEq {x y : α} (h : x = y) : EqvTerm x y where
  rfl:= h.toHEq

def EqvTerm.ofHEq {α β} {x : α} {y : β} (h : x ~= y) :
    EqvTerm x y where
  rfl:= h

end Transport
