
import Std.Data.HashMap

namespace Std.HashMap

variable [BEq α] [Hashable α]

def modify? (m : HashMap α β) (k : α) (f : β → β) : HashMap α β :=
match m.find? k with
| none => m
| some v => m.insert k (f v)

def modifyD (m : HashMap α β) (d : β) (k : α) (f : β → β) :
    HashMap α β :=
m.insert k (f <| m.findD k d)

def map (f : β → β')  (m : HashMap α β) : HashMap α β' :=
m.fold (λ m k v => m.insert k (f v)) mkHashMap

end Std.HashMap

namespace List
section HashMap
open Std Std.HashMap
variable [BEq α] [Hashable α]

def toHashMap (xs : List (α × β)) : HashMap α β :=
xs.foldl (λ m (k,v) => m.insert k v) mkHashMap

end HashMap
end List
