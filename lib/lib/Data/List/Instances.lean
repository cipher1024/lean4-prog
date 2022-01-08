
import Lib.Data.Traversable
import Lib.Data.List.Basic

namespace List

instance : Traversable List where
  map := Functor.map
  traverse := List.mapA
  mapM := List.mapM
  foldl := List.foldl
  foldr := List.foldr
  toList := id
  length := List.length

@[simp]
theorem foldMap_nil [Monoid ω] (f : α → ω) :
  Foldable.foldMap f [] = One.one := rfl

@[simp]
theorem foldMap_cons [Monoid ω] (f : α → ω) x xs :
  Foldable.foldMap f (x :: xs) =
  Foldable.foldMap f xs * f x := by
simp [Foldable.foldMap, Foldable.foldl, foldl]
symmetry
apply foldl_sim (SIM := (. * f x = .))
. simp
intros; simp [*]

instance : LawfulFoldable List where
  foldl_sim :=  by
    intros; apply List.foldl_sim <;> auto
  toArray_toList := sorry
  length_toList := by
    intros; simp [Array.toList]; refl
  foldl_toList := by
    intros; simp [Array.toList]; refl
  foldr_eq_foldMap := by
    intros; simp [Foldable.foldr]
    next f x x₀ =>
    induction x generalizing x₀ <;> simp [foldr, *]

open Traversable
instance : LawfulTraversable List where
  map_eq_traverse := by
    intros; simp [(.<$>.), traverse];
    next x =>
    induction x <;> simp [List.map, List.mapA, *, Seq.seq]
     <;> refl
  traverse_eq_mapM := by
    intros; simp [traverse, mapM]
    next x =>
    induction x <;>
      simp [*, List.mapM, List.mapA, seq_eq_bind, map_eq_pure_bind, Traversable.mapM]
  map_const := by intros; ext; next x =>
    simp [(.∘.), (.<$>.)];
    induction x <;> simp [*, List.map, Functor.mapConst]
  id_map := by intros; simp [(.<$>.)]; next x =>
    induction x <;> simp [List.map, *]
  comp_map := by intros; simp [(.<$>.)]; next x =>
    induction x <;> simp [List.map, *]
  comp_traverse := by
    intros; simp [traverse]
    next x f g => admit
    -- induction x <;> simp [*, List.mapA, comp_lam]
    -- rw [Comp.run_seq]
    -- rw [Comp.run_map, ← comp_map]
    -- simp [*, (.∘.), seq_assoc]; congr
  foldl_eq_traverse := by
    intros; simp [Foldable.foldl, traverse]
    next x x₀ =>
    induction x generalizing x₀
    <;> simp [List.foldl, List.mapA, *]
  traverse_sim := by
    intros; next x R f g h =>
    simp [traverse]
    induction x <;> simp [List.mapA] <;> auto

end List
