
import Sat.Lib.Nat

namespace Array

@[inline]
def foldlIdx (ar : Array α) (f : Nat → α → β → β) (x₀ : β) : β :=
(ar.foldl (λ ⟨x, i⟩ y => ⟨f i y x, i+1⟩) (x₀, 0)).1

@[inline]
unsafe def foldlIdxUnsafe (ar : Array α) (f : Fin ar.size → α → β → β) (x₀ : β) : β :=
(ar.foldl (λ ⟨x, i⟩ y => ⟨f (unsafeCast i) y x, i+1⟩) (x₀, 0)).1

def Fin.succ {n} : Fin n → Fin n
| ⟨i, h⟩ => ⟨i.succ % n, Nat.mod_lt _ $ Nat.lt_of_le_of_lt (Nat.zero_le _) h⟩

@[implementedBy foldlIdxUnsafe]
def foldlIdx' (ar : Array α) (f : Fin ar.size → α → β → β) (x₀ : β) : β :=
if h : 0 < ar.size then
  (ar.foldl (λ ⟨x, i⟩ y => ⟨f i y x, Fin.succ i⟩) (x₀, ⟨0, h⟩)).1
else x₀

@[simp]
def size_map (f : α → β) (ar : Array α) :
  (ar.map f).size = ar.size := sorry

attribute [simp] size_set

@[simp]
def get_map (f : α → β) (ar : Array α) (i : Fin _) :
  (ar.map f).get i = f (ar.get $ ⟨i.1, (size_map f ar) ▸ i.2⟩) := sorry

@[simp]
def size_modify [Inhabited α] (f : α → α)
    (ar : Array α) (i : Nat) :
  (ar.modify i f).size = ar.size := sorry

@[simp]
def size_zipWith (f : α → β → γ) (ar₀ : Array α) (ar₁ : Array β) :
  size (ar₀.zipWith ar₁ f) = min (size ar₀) (size ar₁) := sorry


@[simp] theorem bind_pure' [Monad m] [LawfulMonad m] (x : m α) : x >>= (λ a => pure a) = x := by
  show x >>= (fun a => pure (id a)) = x
  rw [bind_pure_comp, id_map]

attribute [auto] Nat.zero_le

section foldlM_sim
variable {m : Type u → Type u'} [Monad m] [LawfulMonad m]
variable {m' : Type v → Type v'} [Monad m'] [LawfulMonad m']
variable (f : β → α → m β) (g : γ → α → m' γ)
variable (x₀ : β) (y₀ : γ) (h : β → γ)
variable (SIM : m β → m' γ → Prop)

attribute [simp] bind_pure

theorem foldlM_sim (ar : Array α) {x₀ y₀}
        (H₀ : SIM x₀ y₀)
        (Hstep : ∀ x x' a, SIM x x' →
          SIM (x >>= (f . a)) (x' >>= (g . a))) :
  SIM (x₀ >>= ar.foldlM f) (y₀ >>= ar.foldlM g) := by
suffices H :
    ∀ i j, i ≤ j → j ≤ ar.size →
    SIM (x₀ >>= (ar.foldlM f . i j)) (y₀ >>= (ar.foldlM g . i j))
  by apply H <;> auto
intros i j Hij Hj; simp [foldl, foldlM, *]
generalize j - i = n
induction n generalizing x₀ y₀ i j;
focus
  have := Nat.zero_le (size ar)
  simp [foldl, foldlM, *, foldlM.loop, Nat.zero_sub]
  split <;> simp [bind_pure, *]
next n ih =>
  simp only [*, foldlM.loop]
  split
  focus
    rw [← bind_assoc, ← bind_assoc]
    auto
  focus
    simp [*]

theorem foldlM_hom (ar : Array α) {x₀ y₀} (h : m β → m' γ)
        (H' : h x₀ = y₀)
        (H : ∀ x y, h (x >>= (f . y)) = h x >>= (g . y)) :
  h (x₀ >>= ar.foldlM f) = y₀ >>= ar.foldlM g := by
let SIM x y := h x = y
apply foldlM_sim (SIM := SIM)
. assumption
. intros _ _ _ H₂; simp [H, H₂]

theorem foldlM_hom' (ar : Array α) {x₀ y₀} (h : m β → m' γ)
        (H' : h (pure x₀) = pure y₀)
        (H : ∀ x y, h (x >>= (f . y)) = h x >>= (g . y)) :
  h (ar.foldlM f x₀) = ar.foldlM g y₀ := by
let SIM x y := h x = y
have := foldlM_hom (H := H) (H' := H')
simp at this; auto

end foldlM_sim

variable (f : β → α → β) (g : γ → α → γ)
variable (x₀ : β) (y₀ : γ) (h : β → γ)
variable (SIM : β → γ → Prop)

theorem foldl_sim (ar : Array α)
        (H' : SIM x₀ y₀)
        (H : ∀ x x' a, SIM x x' →  SIM (f x a) (g x' a)) :
  SIM (ar.foldl f x₀) (ar.foldl g y₀) := by
apply foldlM_sim (m := Id) (m' := Id) (SIM := SIM)
<;> assumption

theorem foldl_hom (ar : Array α)
        (H' : h x₀ = y₀)
        (H : ∀ x y, h (f x y) = g (h x) y) :
  h (ar.foldl f x₀) = ar.foldl g y₀ := by
subst H'
suffices H :
    ∀ i j, i ≤ j → j ≤ ar.size →
    h (ar.foldl f x₀ i j) = ar.foldl g (h x₀) i j
  by apply H <;> auto
intros i j Hij Hj; simp [foldl, foldlM, *]
generalize j - i = n
induction n generalizing x₀ i j;
focus
  have := Nat.zero_le (size ar)
  simp [foldl, foldlM, *, foldlM.loop, Nat.zero_sub]
  byCases h : i < j <;> simp [*] <;> refl
next n ih =>
  simp [*, foldlM.loop]
  split
  . rw [← H, ← ih] <;> assumption
  . refl

def mapA {F} [Applicative F] (f : α → F β) (ar : Array α) : F (Array β) :=
ar.foldl (λ acc x => Array.push <$> acc <*> f x) (pure $ Array.mkEmpty ar.size)

theorem mapA_eq_mapM {m} [Monad m] [LawfulMonad m] (f : α → m β) (ar : Array α) :
  ar.mapA f = ar.mapM f := by
simp only [mapA, mapM, foldl]
apply Array.foldlM_hom' (m := Id) (m' := m) (h := Id.run)
. refl
focus
  intros; simp [seq_eq_bind_map, map_eq_pure_bind]
  refl

end Array

structure Buffer (m α) where
mkImpl ::
  cells : Array α
  Hsize : cells.size = m

namespace Buffer

def mk (ar : Array α) : OptionM (Buffer m α) :=
if h : ar.size = m then return ⟨ar, h⟩
else none

@[inline]
def get (ar : Buffer m α) (i : Fin m) : α :=
ar.cells.get $ ar.Hsize.symm ▸ i

@[inline]
def set (i : Fin m) (x : α) (ar : Buffer m α) : Buffer m α where
  cells := ar.cells.set (ar.Hsize.symm ▸ i) x
  Hsize := by simp [ar.Hsize]

@[specialize]
def map (f : α → β) (ar : Buffer m α) : Buffer m β where
  cells := ar.cells.map f
  Hsize := by simp [ar.Hsize]

@[inline]
def modify (i : Fin m) (f : α → α) (ar : Buffer m α) : Buffer m α :=
ar.set i (f $ ar.get i)

def foldl (ar : Buffer n α) (f : α → β → β) (x₀ : β) : β :=
ar.cells.foldl (flip f) x₀

def foldlIdx (ar : Buffer n α) (f : Fin n → α → β → β) (x₀ : β) : β :=
ar.cells.foldlIdx' (λ i => f $ ar.Hsize ▸ i) x₀

def mkFilled (x : α) : Buffer n α :=
⟨ Array.mkArray n x , by simp ⟩

def zipWith (f : α → β → γ)
  (b₀ : Buffer n α) (b₁ : Buffer n β) : Buffer n γ :=
⟨ b₀.cells.zipWith b₁.cells f, by simp [Buffer.Hsize]; refl ⟩

end Buffer

structure Grid (m n α) where
mkImpl ::
  cells : Buffer m (Buffer n α)

namespace Grid

variable {m n : Nat} {α β : Type _}

def mk (ar : Array (Array α)) : OptionM (Grid m n α) := do
Grid.mkImpl <$> Buffer.mk (← ar.mapM Buffer.mk)

@[inline]
def get (ar : Grid m n α) (i : Fin m) (j : Fin n) : α :=
ar.cells.get i |>.get j

@[specialize]
def map (f : α → β) (g : Grid m n α) : Grid m n β where
  cells := g.cells.map $ Buffer.map f

@[inline]
def set (i : Fin m) (j : Fin n) (x : α) (g : Grid m n α) : Grid m n α where
  cells := g.cells.modify i $ Buffer.set j x

@[inline]
def modify (i : Fin m) (j : Fin n) (f : α → α) (g : Grid m n α) : Grid m n α where
  cells := g.cells.modify i $ Buffer.modify j f

@[inline]
def foldl (ar : Grid m n α) (f : α → β → β) (x₀ : β) : β :=
ar.cells.foldl (λ ar => ar.foldl f) x₀

@[inline]
def foldlIdx (ar : Grid m n α) (f : Fin m → Fin n → α → β → β) (x₀ : β) : β :=
ar.cells.foldlIdx (λ i ar => ar.foldlIdx $ f i) x₀

def zipWith (f : α → β → γ)
    (ar₀ : Grid m n α) (ar₁ : Grid m n β) : Grid m n γ :=
⟨ ar₀.cells.zipWith (Buffer.zipWith f) ar₁.cells ⟩

end Grid
