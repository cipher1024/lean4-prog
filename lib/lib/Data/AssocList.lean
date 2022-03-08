
import Std.Data.AssocList

namespace Std.AssocList
open Std

def keys : AssocList α β → List α
| nil => []
| cons k x xs => k :: keys xs

@[simp]
def length : AssocList α β → Nat
| nil => 0
| cons _ _ l => l.length.succ

@[simp]
theorem keys_mapVal (xs : AssocList k α) (f : α → β) :
  (xs.mapVal f).keys = xs.keys := by
induction xs with
| nil => simp [mapVal]; rfl
| cons k x xs => simp [keys, mapVal, *]

section mapFilter
variable (f : k → α → Option β)

def mapFilter :
  AssocList k α → AssocList k β
| nil => nil
| cons i x xs =>
  let xs' := mapFilter xs
  match f i x with
  | none => xs'
  | some x' => cons i x' xs'

-- @[simp]
-- theorem keys_mapFilter (xs : AssocList k α) :
--   (xs.mapFilter f).keys = xs.keys := by
-- induction xs with
-- | nil => simp [mapFilter]; rfl
-- | cons k x xs =>
--   simp [mapFilter]
--   cases f k x <;> simp [keys, *]


end mapFilter

section DecidableEq

variable [DecidableEq α]

def eraseAll (x : α) : AssocList α β → AssocList α β
| nil => nil
| cons k v xs =>
  let xs' := eraseAll x xs
  if x = k then xs'
  else cons k v xs'

end DecidableEq

end Std.AssocList
