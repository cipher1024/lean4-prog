
import Std.Data.HashMap

namespace List
section HashMap
open Std Std.HashMap
variable [BEq α] [Hashable α]

def toHashMap (xs : List (α × β)) : HashMap α β :=
xs.foldl (λ m (k,v) => m.insert k v) mkHashMap

end HashMap
end List
