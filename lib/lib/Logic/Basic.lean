
import Lib.Tactic

theorem ite_pos [h : Decidable p] (hp : p) {x y : α} :
  ite p x y = x := by
cases h <;> auto

theorem ite_neg [h : Decidable p] (hp : ¬ p) {x y : α} :
  ite p x y = y := by
cases h <;> auto

@[simp]
theorem decide_eq_true_iff {h : Decidable p} :
  decide p = true ↔ p :=
⟨of_decide_eq_true, decide_eq_true⟩

@[simp]
theorem decide_eq_false_iff {h : Decidable p} :
  decide p = false ↔ ¬ p :=
⟨of_decide_eq_false, decide_eq_false⟩

theorem Eq.comm {x y : α} :
  x = y ↔ y = x := by
constructor
<;> intros h
<;> subst h
<;> rfl

theorem not_iff_not {p q : Prop} :
  (p ↔ q) → (¬ p ↔ ¬ q) :=
by intros h; rw [h]; refl
