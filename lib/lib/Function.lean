
import Lib.Tactic

def Injective (f : α → β) :=
∀ x y, f x = f y → x = y

def Surjective (f : α → β) :=
∀ y, ∃ x, f x = y

abbrev LeftInv (f : α → β) (g : β → α) :=
g ∘ f = id

theorem LeftInv.apply {f : α → β} {g} (H : LeftInv f g) x :
  g (f x) = x := congrFun H x

abbrev RightInv (f : α → β) (g : β → α) :=
f ∘ g = id

theorem RightInv.apply {f : α → β} {g} (H : RightInv f g) x :
  f (g x) = x := congrFun H x

def HasLeftInv (f : α → β) :=
∃ g, LeftInv f g

@[auto]
theorem HasLeftInv.intro (f : α → β) {g}
  (H : LeftInv f g) : HasLeftInv f :=
⟨ g, H ⟩

abbrev LeftInv.toHasLeftInv := @HasLeftInv.intro

def HasRightInv (f : α → β) :=
∃ g, RightInv f g

@[auto]
theorem HasRightInv.intro (f : α → β) {g}
  (H : RightInv f g) : HasRightInv f :=
⟨ g, H ⟩

abbrev RightInv.toHasRightInv := @HasRightInv.intro

noncomputable def inv [Nonempty α] (f : α → β) (b : β) :=
Classical.epsilon λ a => f a = b

theorem inv_comp_of_injective [Nonempty α] {f : α → β}
        (h : Injective f) :
  inv f ∘ f = id := by
apply funext; intros x; simp [inv]
apply h
apply Classical.epsilon_spec (p := λ y => f y = f x)
exists x

theorem comp_inv_of_surjective [Nonempty α] {f : α → β}
        (h : Surjective f) :
  f ∘ inv f = id := by
apply funext; intros x; simp [inv]
apply Classical.epsilon_spec (p := λ y => f y = x)
apply h

@[auto]
theorem HasLeftInv_of_Injective [Nonempty α] {f : α → β}
        (h : Injective f) :
  HasLeftInv f := by
exists inv f; apply inv_comp_of_injective h

@[auto]
theorem Injective_of_LeftInv {f : α → β} {g}
        (hg : LeftInv f g) :
  Injective f := by
intros x y Hxy
rw [← hg.apply x, Hxy, hg.apply]

@[auto]
theorem Injective_of_HasLeftInv  {f : α → β}
        (h : HasLeftInv f) :
  Injective f := by
obtain ⟨g,hg⟩ from h;
apply Injective_of_LeftInv; assumption

theorem HasLeftInv_iff_Injective [Nonempty α] {f : α → β} :
  HasLeftInv f ↔ Injective f := by auto

@[auto]
theorem HasRightInv_of_Surjective [Nonempty α] {f : α → β}
        (h : Surjective f) :
  HasRightInv f := by
exists inv f; apply comp_inv_of_surjective h

@[auto]
theorem Surjective_of_RightInv {f : α → β} {g}
        (hg : RightInv f g) :
  Surjective f := by
intros x
exists g x; rw [hg.apply]

@[auto]
theorem Surjective_of_HasRightInv {f : α → β}
        (h : HasRightInv f) :
  Surjective f := by
obtain ⟨g, hg⟩ from h;
apply Surjective_of_RightInv; assumption

theorem HasRightInv_iff_Surjective [Nonempty α] {f : α → β} :
  HasRightInv f ↔ Surjective f := by auto

@[simp]
theorem flip_eq {α β γ} (f : α → β → γ) x y :
  flip f x y = f y x := rfl

@[simp]
theorem flip_flip {α β γ} (f : α → β → γ) :
  flip (flip f) = f := rfl

theorem comp_lam {α β γ} (f : α → β) (g : β → γ) :
  (g ∘ λ a => f a) = λ a => g (f a) := rfl

@[simp]
def curry (f : α × β → γ) (x : α) (y : β) := f (x, y)

@[simp]
def uncurry (f : α → β → γ) : α × β → γ
| (x, y) => f x y
