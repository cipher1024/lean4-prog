
import Std.Data.HashSet

namespace List
section HashSet
open Std Std.HashSet
variable [BEq α] [Hashable α]

def toHashSet (xs : List α) : HashSet α :=
xs.foldl HashSet.insert mkHashSet

end HashSet
end List
