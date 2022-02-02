
import Lib.Tactic

theorem ite_pos [h : Decidable p] (hp : p) {x y : α} :
  ite p x y = x := by
cases h <;> auto

theorem ite_neg [h : Decidable p] (hp : ¬ p) {x y : α} :
  ite p x y = y := by
cases h <;> auto
