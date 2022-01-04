
import Lib.Tactic

namespace Prod
variable {α α' β β'} (x y : α × β)
variable {f : α → α'} {g : β → β'}

def eta :
  x.1 = y.1 →
  x.2 = y.2 →
  x = y := by
cases x; cases y; simp <;> auto

@[simp]
theorem fst_map : (x.map f g).1 = f x.1 :=
by cases x; refl

@[simp]
theorem snd_map : (x.map f g).2 = g x.2 :=
by cases x; refl

end Prod
