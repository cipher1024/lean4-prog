
import Sat.Lib.Traversable
import Sat.Lib.List.Basic

namespace List

instance : Traversable List where
  map := Functor.map
  traverse := List.mapA
  mapM := List.mapM
  foldl := List.foldl
  toList := id
  length := List.length

variable {α β γ : Type u} {f : β → α → β} {g : γ → α → γ}
variable {SIM : β → γ → Prop}
variable {x₀ y₀} (t : List α)

theorem foldl_sim :
    SIM x₀ y₀ →
    (∀ a x y, SIM x y → SIM (f x a) (g y a)) →
    SIM (foldl f x₀ t) (foldl g y₀ t) := by
induction t generalizing x₀ y₀ <;> auto

instance : LawfulFoldable List where
  foldl_sim :=  by
    intros; apply List.foldl_sim <;> auto
  toArray_toList := sorry
  length_toList := by
    intros; simp [Array.toList]; refl
  foldl_toList := by
    intros; simp [Array.toList]; refl

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
