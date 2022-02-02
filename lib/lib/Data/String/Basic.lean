
import Lib.Data.MonoFunctor
import Lib.Data.MonoFoldable
import Lib.Data.MonoTraversable
import Lib.Data.List.Instances

namespace String

@[implementedBy map]
def map' (f : Char → Char) : String → String
| ⟨ data ⟩ => ⟨ Functor.map f data ⟩

instance : MonoFunctor String Char where
  map := map'

instance : LawfulMonoFunctor String Char where
  id_map := by
    intros; next x =>
    cases x; simp [MonoFunctor.map, map']
  comp_map := by
    intros; next x =>
    cases x; simp [MonoFunctor.map, map']

variable {β : Type}

@[inline]
def foldlImpl (f : β → Char → β) (x₀ : β) : String → β :=
String.foldl f x₀

@[implementedBy foldlImpl]
def foldl' (f : β → Char → β) (x₀ : β) : String → β
| ⟨ data ⟩ => Foldable.foldl f x₀ data

@[inline]
def foldrImpl (f : Char → β → β) (x₀ : β) : String → β :=
String.foldr f x₀

@[implementedBy foldrImpl]
def foldr' (f : Char → β → β) (x₀ : β) : String → β
| ⟨ data ⟩ => Foldable.foldr f x₀ data

def toArray (s : String) : Array Char :=
String.foldl' Array.push (Array.mkEmpty s.length) s

instance : MonoFoldable String Char where
  foldl := String.foldl'
  foldr := String.foldr'
  toList := String.toList
  toArray := String.toArray
  length := String.length

open MonoFoldable

instance : LawfulMonoFoldable String Char where
  foldl_sim :=
    by intros _ _ _ f SIM x₀ y₀ t a ih
       cases t; simp [foldl, MonoFoldable.foldl]
       auto [LawfulFoldable.foldl_sim]
  foldr_eq_foldMap :=
    by intros _ _ t _
       cases t; simp [foldr, MonoFoldable.foldr]
       auto [LawfulFoldable.foldr_eq_foldMap]
  toArray_toList :=
    by intros t
       cases t with | mk data =>
       simp [toList, toArray, String.foldl']
       simp [String.toList,
             String.toArray, String.foldl']
       show Foldable.toArray data = _
       rw [LawfulFoldable.toArray_eq]
       refl
  length_toList := by
    intros t; cases t; refl
  foldl_toList := by
    intros β f x₀ t; cases t; refl

section mapM

variable {M} [Monad M]
@[specialize] partial def mapMAux (f : Char → M Char) (i : Pos) (s : String) : M String :=
  if s.atEnd i then s
  else do
    let c ← f (s.get i)
    let s := s.set i c
    mapMAux f (s.next i) s

@[inline] def mapMImpl (f : Char → M Char) (s : String) : M String :=
  mapMAux f 0 s

@[implementedBy mapMImpl] def mapM (f : Char → M Char) (s : String) : M String :=
  String.mk <$> s.data.mapM f

end mapM


section mapM

variable {F} [Applicative F]

def mapA (f : Char → F Char) (s : String) : F String :=
String.mk <$> Traversable.traverse f s.data

end mapM

instance : MonoTraversable String Char where
  traverse := mapA
  mapM := mapM

open LawfulMonoTraversable
instance : LawfulMonoTraversable String Char where
  map_eq_traverse := by
    intros; next x => cases x with | mk data =>
    simp [MonoTraversable.traverse, MonoFunctor.map, map']
    simp [LawfulTraversable.map_eq_traverse]; refl
  foldl_eq_traverse := by
    intros; next x y => cases x with | mk data =>
    simp [MonoFoldable.foldl, foldl']
    simp [LawfulTraversable.foldl_eq_traverse]; refl
  traverse_eq_mapM := by
    intros; next x => cases x with | mk data =>
    simp [MonoTraversable.traverse, mapA]
    simp [LawfulTraversable.traverse_eq_mapM]; refl
  comp_traverse := by
    intros; next x y z => cases x with | mk data =>
    simp [MonoTraversable.traverse, mapA]
    simp [LawfulTraversable.comp_traverse]; refl
  traverse_sim := by
    intros; next x SIM _ _ _ => cases x with | mk data =>
    simp [MonoTraversable.traverse, mapA]
    auto [LawfulTraversable.traverse_sim, ApplicativeRel.naturality]

end String
