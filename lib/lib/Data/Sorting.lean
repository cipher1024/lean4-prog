
import Lib.Data.AssocList
import Lib.Data.Nat
import Lib.Meta.DeclGraph
import Lib.Tactic

import Std.Data.AssocList

namespace Ordering
variable [DecidableEq α]

-- theorem lt_iff_compare_eq_lt [LT α] (x y : α) [Decidable (x < y)] :
--   x < y ↔ compareOfLessAndEq x y = Ordering.lt := by
--   simp [compareOfLessAndEq]
--   split
--   focus
--     auto
--   byCases h : x = y
--   focus
--     rw [ite_pos h]
--     constructor; auto
--     intro h; injection h
--   focus
--     rw [ite_neg h]
--     constructor; auto
--     intro h; injection h

-- theorem eq_iff_compare_eq_eq (x y : Nat) :
--   x = y ↔ (compareOfLessAndEq x y) = Ordering.eq := by
--   simp [compareOfLessAndEq]
--   byCases h : x < y
--   focus
--     rw [ite_pos h]
--     constructor <;> intros h'
--     focus
--       subst h'
--       cases Nat.lt_irrefl _ h
--     focus
--       cases h'
--   focus
--     rw [ite_neg h]
--     constructor <;> intros h'
--     focus rw [ite_pos h']
--     focus
--       byCases h'' : x = y
--       . auto
--       rw [ite_neg h''] at h'
--       cases h'

-- theorem gt_iff_compare_eq_gt (x y : Nat) :
--   y < x ↔ (compareOfLessAndEq x y) = Ordering.gt := by
-- simp [compareOfLessAndEq]
-- byCases h : x < y
-- focus
--   rw [ite_pos h]
--   constructor <;> intros h'
--   focus
--     have := Nat.le_antisymm (Nat.le_of_lt h) (Nat.le_of_lt h')
--     subst this
--     cases Nat.lt_irrefl _ h
--   focus cases h'
-- focus
--   rw [ite_neg h]
--   constructor <;> intros h'
--   focus
--     rw [ite_neg]
--     intros h; subst h
--     apply Nat.lt_irrefl _ h'
--   focus
--     have : ¬ x = y := by
--       intro h; rw [ite_pos h] at h'
--       cases h'
--     rw [ite_neg] at h' <;> try auto
--     have : ¬ y = x := λ h => this h.symm
--     auto [Nat.le_of_not_gt, Nat.lt_of_le_of_ne]

-- @[simp]
-- theorem compare_eq_lt_iff (x y : Nat) :
--   (compare x y) = Ordering.lt ↔ x < y := by
-- rw [lt_iff_compare_eq_lt]; refl

-- @[simp]
-- theorem compare_eq_eq_iff (x y : Nat) :
--   (compare x y) = Ordering.eq ↔ x = y := by
-- rw [eq_iff_compare_eq_eq]; refl

-- @[simp]
-- theorem compare_eq_gt_iff (x y : Nat) :
--    (compare x y) = Ordering.gt ↔ y < x := by
-- rw [gt_iff_compare_eq_gt]; refl

end Ordering


inductive All (P : α → Prop) : List α → Prop where
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

inductive Sorted (R : α → α → Prop) : List α → Prop where
  | nil : Sorted R []
  | single : Sorted R [x]
  | cons1 {x x'} {xs} :
    R x x' →
    Sorted R (x' :: xs) →
    Sorted R (x :: x' :: xs)

inductive Sorted2 (R : α → α → Prop) : List α → Prop where
  | nil : Sorted2 R []
  | cons {x xs} :
    All (R x) xs →
    Sorted2 R xs →
    Sorted2 R (x :: xs)
