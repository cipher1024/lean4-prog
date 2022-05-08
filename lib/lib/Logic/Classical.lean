
import Lib.Tactic

namespace Decidable

variable {P Q} [Hdec : Decidable P]
variable (h : P ↔ Q)

def congr : Decidable Q :=
match Hdec with
| isTrue hp => isTrue <| h.mp hp
| isFalse hnp => isFalse <| mt h.mpr hnp

end Decidable


namespace Classical

theorem iff_iff_and_or_and {p q} :
  (p ↔ q) ↔ (p ∧ q) ∨ (¬ p ∧ ¬ q) := by
constructor <;> intros h
. simp [h, and_self, Classical.em]
. cases h <;> auto

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

@[simp low]
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

@[simp mid]
theorem not_implies {p q : Prop} :
  ¬ (p → q) ↔ p ∧ ¬ q := by
rw [not_forall]
constructor <;> intros h <;> cases h
<;> constructor <;> assumption

@[simp]
theorem not_not (p : Prop) : ¬ ¬ p ↔ p := by
constructor <;> intros h
next =>
  apply byContradiction; intro h'
  apply (h h')
next =>
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

theorem not_and_iff_implies (p q : Prop) : ¬ (p ∧ q) ↔ p → ¬ q := by
rw [not_and]
by_cases h : p <;>
simp only [h, false_or, true_or, true_implies, false_implies, iff_self]

theorem not_implies_self_implies :
  (¬ p → p) → p := by
by_cases h : p <;> auto

macro "negate_goal " h:ident : tactic =>
  `(apply not_implies_self_implies; intro $h)

end Classical
