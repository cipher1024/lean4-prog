
import Lib.Data.Functor
import Lib.Data.List.Instances

class MonoFunctor (F : Type u) (α : outParam (Type v)) where
  map : (α → α) → F → F

instance {F} [Functor F] : MonoFunctor (F α) α where
  map := Functor.map

open MonoFunctor
class LawfulMonoFunctor (F : Type u) (α : outParam (Type v))
      [outParam (MonoFunctor F α)] where
  id_map (x : F) : map id x = x
  comp_map (g h : α → α) (x : F) :
    map (h ∘ g) x = map h (map g x)

instance {F} [Functor F] [LawfulFunctor F] :
         LawfulMonoFunctor (F α) α where
  id_map := LawfulFunctor.id_map
  comp_map := LawfulFunctor.comp_map
