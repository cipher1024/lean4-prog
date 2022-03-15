
import Std.Data.AssocList
import Lib.Data.Foldable

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
def foldr (f : ι → α → β → β) (x₀ : β) : AssocList ι α → β
| nil => x₀
| cons k x xs => f k x (foldr f x₀ xs)

instance : IdxFoldable ι (AssocList ι) where
  foldl := foldl
  foldr := foldr

instance : LawfulIdxFoldable ι (AssocList ι) where
  foldl_sim := by
    intros; next SIM x₀ y₀ xs h₀ ih =>
    simp [IdxFoldable.foldl, foldl, Id.run]
    induction xs generalizing x₀ y₀
    <;> simp [foldlM, *]

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
