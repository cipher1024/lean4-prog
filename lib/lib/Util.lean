
syntax term " =@{" term "} " term : term

macro_rules
| `($x =@{ $t } $y) => `(@Eq $t $x $y)

-- TODO: Move this
class Elem (α : outParam <| Type u) (β : Type v) where
  elem : α → β → Prop

infix:30 " ∈ " => Elem.elem

class SubsetEq (α : Type u) where
  subsetEq : α → α → Prop

infix:30 " ⊆ " => SubsetEq.subsetEq
