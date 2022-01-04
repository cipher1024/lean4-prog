
import Lib.Tactic

namespace Classical

@[simp]
theorem not_exists (p : α → Prop) :
  ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by
constructor <;> intros h
focus
  intros x Hp
  apply h; clear h
  exists x; assumption
focus
  intros h'
  cases h' with | intro y h' =>
  apply (h _ h')

@[simp]
theorem not_forall (p : α → Prop) :
  ¬ (∀ x, p x) ↔ ∃ x, ¬ p x := by
constructor <;> intros h
focus
  apply byContradiction; intros h₀
  apply h; clear h; intro x
  apply byContradiction; intros h₁
  apply h₀; clear h₀
  exists x; assumption
focus
  intros h₀
  cases h with | intro x h =>
  apply h; clear h
  apply h₀

@[simp]
theorem not_not (p : Prop) : ¬ ¬ p ↔ p := by
constructor <;> intros h
focus
  apply byContradiction; intros h'
  apply (h h')
focus
  intros h'
  apply h' h

@[simp]
theorem not_iff_not (p q : Prop) :
  (¬ p ↔ ¬ q) ↔ (p ↔ q) := by
constructor <;> intros h
focus
  rw [← not_not p, h, not_not]
  apply Iff.refl
focus
  rw [h]
  apply Iff.refl

@[simp]
theorem not_or (p q : Prop) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by
constructor
focus
  intros h₀; constructor <;>
    intros h₁ <;>
    apply h₀
  { left; assumption }
  { right; assumption }
focus
  intros h hpq; cases h with | intro hp hq =>
  cases hpq <;> contradiction

@[simp]
theorem not_and (p q : Prop) : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := by
rw [← not_iff_not, not_or]
repeat rw [not_not]
apply Iff.refl

end Classical
