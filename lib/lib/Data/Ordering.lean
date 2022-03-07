import Lib.Tactic

namespace Ordering

def flip : Ordering → Ordering
| lt => gt
| eq => eq
| gt => lt

instance : DecidableEq Ordering
  | x, y => by
cases x <;> cases y <;>
first
 | apply isTrue; refl
 | apply isFalse;
   intro h; cases h

inductive Spec {α} [LT α] (x y : α) : Ordering → Type
| isLT : x < y → Spec x y lt
| isEQ : x = y → Spec x y eq
| isGT : y < x → Spec x y gt

end Ordering

inductive POrdering [LT α] (x y : α) : Type
| isLT : x < y → POrdering x y
| isEQ : x = y → POrdering x y
| isGT : y < x → POrdering x y

namespace POrdering
open Ordering
variable [LT α]

@[inline]
def toOrdering {x y : α} : POrdering x y → Ordering
| isLT h => lt
| isEQ h => eq
| isGT h => gt

end POrdering
