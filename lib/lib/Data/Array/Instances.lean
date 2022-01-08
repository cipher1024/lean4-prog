import Lib.Data.Array.Basic
import Lib.Data.List.Instances
import Lib.Data.Traversable

namespace Array

instance : Foldable Array where
  foldr := Array.foldr
  foldl := Array.foldl
  toArray := id
  toList := Array.toList
  length := Array.size

instance : Traversable Array where
  map := Array.map
  traverse := Array.mapA
  mapM := Array.mapM

@[simp]
theorem map_toList {α β : Type _} (f : α → β) (ar : Array α) :
  f <$> ar.toList = (f <$> ar).toList := by
-- have : f <$> ar = Array.map f ar := rfl
-- rw [this]; simp [map, mapM]
suffices f <$> toList ar =
         toList (foldl (fun bs a => push bs (f a))
                       (mkEmpty (size ar)) ar)
  from this
rw [← foldl_toList]
have : toList (Foldable.foldl (fun bs a => push bs (f a)) (mkEmpty (size ar)) (toList ar)) =
       Foldable.foldl (fun bs a => bs ++ [f a]) [] (toList ar) := by
     apply LawfulFoldable.foldl_hom (h := toList)
     <;> simp
simp only [Foldable.foldl] at this
rw [this]; clear this
generalize toList ar = ys
trans ([] ++ f <$> ys)
. simp
suffices ∀ xs,
  xs ++ f <$> ys = List.foldl (fun bs a => bs ++ [f a]) xs ys
  by apply this
intros xs
induction ys generalizing xs
<;> simp [List.foldl]
next y ys ih =>
simp [← ih, List.append_assoc]

instance : LawfulFoldable Array where
  foldl_sim :=  by
    intros; apply Array.foldl_sim <;> auto
  toArray_toList := sorry
  length_toList :=
    by intros; simp [toList]; sorry
  foldl_toList := by
    intros; simp [toList, foldl]; sorry
  foldr_eq_foldMap := sorry

instance : LawfulFunctor Array := sorry

instance : LawfulTraversable Array := by
apply LawfulTraversable_of_hom (T₀ := List) (T₁ := Array)
  (g := @List.toArray)
  (f := @Array.toList)
focus
  intros; ext;
  simp
focus
  intros; ext;
  simp
focus
  intros; ext;
  simp
all_goals admit

end Array
