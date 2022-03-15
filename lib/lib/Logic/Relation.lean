
class Reflexive (R : α → α → Prop) where
  refl x : R x x

class Symmetric (R : α → α → Prop) where
  symmetry {x y} : R x y → R y x

instance : @Reflexive α (.=.) where
  refl _ := rfl

instance : Reflexive (.↔.) where
  refl _ := Iff.rfl

instance : @Symmetric α (.=.) where
  symmetry := Eq.symm

instance : Symmetric (.↔.) where
  symmetry := Iff.symm

instance : Reflexive (.→.) where
  refl _ := id

instance : @Reflexive Nat LE.le where
  refl := Nat.le_refl

instance : @Trans Nat Nat Nat LE.le LE.le LE.le where
  trans := Nat.le_trans

instance : @Trans Nat Nat Nat LT.lt LT.lt LT.lt where
  trans := Nat.lt_trans

instance : @Trans Nat Nat Nat GE.ge GE.ge GE.ge where
  trans h h' := Nat.le_trans h' h

instance : @Trans Nat Nat Nat GT.gt GT.gt GT.gt where
  trans h h' := Nat.lt_trans h' h
