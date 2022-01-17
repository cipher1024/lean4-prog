
import Std.Data.HashSet

namespace Std.HashSet

variable [BEq α] [Hashable α]

def intersect (s₀ s₁ : HashSet α) : HashSet α :=
s₀.fold (λ s x => if s₁.contains x then s.insert x else s)
  mkHashSet

def difference (s₀ s₁ : HashSet α) : HashSet α :=
s₁.fold HashSet.erase s₀

def union (s₀ s₁ : HashSet α) : HashSet α :=
s₀.fold HashSet.insert s₁

end Std.HashSet

namespace List
section HashSet
open Std Std.HashSet
variable [BEq α] [Hashable α]

def toHashSet (xs : List α) : HashSet α :=
xs.foldl HashSet.insert mkHashSet

end HashSet
end List
