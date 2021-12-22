
structure Equiv (α β : Type _) where
  to : α → β
  inv : β → α
  to_inv : ∀ x, to (inv x) = x
  inv_to : ∀ x, inv (to x) = x

attribute [simp] Equiv.to_inv Equiv.inv_to

namespace Equiv

def id : Equiv α α where
  to := _root_.id
  inv := _root_.id
  to_inv := by intros; simp
  inv_to := by intros; simp

def comp (f : Equiv β γ) (g : Equiv α β) : Equiv α γ where
  to := f.to ∘ g.to
  inv := g.inv ∘ f.inv
  to_inv := by intros; simp [Function.comp, to_inv]
  inv_to := by intros; simp [Function.comp, inv_to]

def symm (f : Equiv α β) : Equiv β α where
  to := f.inv
  inv := f.to
  to_inv := f.inv_to
  inv_to := f.to_inv

def prodCongr (f : Equiv α β) (g : Equiv α' β') : Equiv (α × α') (β × β') where
  to | (a, b) => (f.to a, g.to b)
  inv | (a, b) => (f.inv a, g.inv b)
  to_inv := by intro x; cases x; simp
  inv_to := by intro x; cases x; simp

section Congr

variable (f : Equiv α β ) (g : Equiv α' β')

@[simp]
theorem to_prodCongr : (prodCongr f g).to x = (f.to x.1, g.to x.2) := rfl

@[simp]
theorem inv_prodCongr : (prodCongr f g).inv x = (f.inv x.1, g.inv x.2) := rfl

end Congr

def left_unitor : Equiv (PUnit × α) α where
  to | (_, a) => a
  inv | a => ((), a)
  to_inv := by intro x; simp
  inv_to := by intro x; cases x; simp

def right_unitor : Equiv (α × PUnit) α where
  to | (a, _) => a
  inv | a => (a, ())
  to_inv := by intro x; simp
  inv_to := by intro x; cases x; simp

section Unitors

@[simp]
theorem to_left_unitor (x : PUnit × β) : left_unitor.to x = x.2 := rfl

@[simp]
theorem inv_left_unitor (x : α) : left_unitor.inv x = ((), x) := rfl

@[simp]
theorem to_right_unitor (x : α × PUnit) : right_unitor.to x = x.1 := rfl

@[simp]
theorem inv_right_unitor (x : α) : right_unitor.inv x = (x, ()) := rfl

end Unitors

def assoc : Equiv ((α × β) × γ) (α × β × γ) where
  to | ((a, b), c) => (a, b, c)
  inv | (a, b, c) => ((a, b), c)
  to_inv := by intro x; cases x; simp
  inv_to := by intro x; cases x; simp

section Assoc

@[simp]
theorem to_assoc (x : (α × β) × γ) : assoc.to x = (x.1.1, x.1.2, x.2) := rfl

@[simp]
theorem inv_assoc (x : α × β × γ) : assoc.inv x = ((x.1, x.2.1), x.2.2) := rfl

end Assoc

local infix:60 " ⊚ " => comp

theorem ext (f g : Equiv α β)
  (H : ∀ x, f.to x = g.to x):
  f = g := by
cases f; cases g; simp
next f f' f_inv f_to =>
next g g' g_inv g_to =>
have : g = f := by apply funext; apply H
exists this; apply funext; intro x
have f_inv := congrArg g' <| f_inv x
rewrite [← this, g_to] at f_inv
apply Eq.symm; assumption

@[simp]
theorem to_id : (@id α).to x = x := rfl

@[simp]
theorem to_comp (f : Equiv α β) (g : Equiv β γ) :
  (g ⊚ f).to x = g.to (f.to x) := rfl

@[simp]
theorem to_symm (f : Equiv α β) :
  (f.symm).to x = f.inv x := rfl

@[simp]
theorem inv_id : (@id α).inv x = x := rfl

@[simp]
theorem inv_comp (f : Equiv α β) (g : Equiv β γ) :
  (g ⊚ f).inv x = f.inv (g.inv x) := rfl

@[simp]
theorem inv_symm (f : Equiv α β) :
  (f.symm).inv x = f.to x := rfl

@[simp]
theorem id_comp (f : Equiv α β) :
  id ⊚ f = f := by
apply ext; intro x; simp

@[simp]
theorem comp_id (f : Equiv α β) :
  f ⊚ id = f := by
apply ext; intro x; simp

@[simp]
theorem comp_assoc (f : Equiv α β) (g : Equiv β γ) (h : Equiv γ ϕ) :
  (h ⊚ g) ⊚ f = h ⊚ (g ⊚ f) := by
apply ext; intro x; simp

@[simp]
theorem symm_id :
  (@id α).symm = id := by
apply ext; intro x; simp

@[simp]
theorem symm_comp (f : Equiv α β) (g : Equiv β γ) :
  (g ⊚ f).symm = f.symm ⊚ g.symm := by
apply ext; intro x; simp

theorem eq_inv_iff (f : Equiv α β) x y :
  x = f.inv y ↔ f.to x = y := by
constructor <;> intros h <;> subst h
<;> simp [*]

end Equiv
