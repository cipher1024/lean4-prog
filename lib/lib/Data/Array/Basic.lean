
import Lib.Data.Nat
import Lib.Data.List.Basic

namespace Array

instance : Functor Array where
  map := Array.map

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
  split <;> simp [bind_pure, *] <;>
  rw [bind_pure, bind_pure] <;> assumption
  done
next n ih =>
  simp only [*, foldlM.loop]
  split
  focus
    rw [← bind_assoc, ← bind_assoc]
    auto
  focus
    simp [*]
  simp only [*, foldlM.loop, bind_pure]
  rw [bind_pure, bind_pure] <;> assumption
  done

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

variable [Monad m] [LawfulMonad m]

local notation "Push" =>
  (λ ar x => (pure <| Array.push ar x))

@[simp]
theorem Array.toSubarray_toArray_eq_nil (ar : Array α) :
  (toSubarray ar i i).toArray = #[] :=
sorry

@[simp]
theorem Array.toSubarray_toArray_eq_self (ar : Array α) :
  (toSubarray ar 0 ar.size).toArray = ar :=
sorry

theorem Array.push_toSubarray (ar : Array α) i h :
  (toSubarray ar 0 i).toArray.push (ar.get ⟨i,h⟩) =
  (toSubarray ar 0 i.succ).toArray :=
sorry

theorem foldlM_eq_self (ar : Array α)  :
  foldlM Push #[] ar =
  (pure ar : m _) := by
simp [foldl, foldlM, Nat.le_refl]
suffices H :
    ∀ i, i ≤ ar.size →
      (ar.foldlM Push ar[:i].toArray i ar.size) =
      (pure ar : m _) by
  specialize H 0 (Nat.zero_le _)
  simp [foldlM, Nat.le_refl] at H; assumption
intros i Hi; simp [foldl, foldlM, *]
generalize Hn : size ar - i = n
induction n generalizing i;
next =>
  have h₀ : ¬ i < size ar := by
    have Hn := Nat.le_of_eq Hn
    -- have Hn := Nat.sub_le Hn
    skip
    admit
  have h₁ : i = size ar := by
    auto [Nat.le_antisymm]
  simp [foldlM.loop, h₀]
  simp [*, Nat.le_refl]
next ih =>
  have h₀ : i < size ar := sorry
  simp [foldlM.loop, h₀, Array.push_toSubarray]
  rw [ih _ h₀]
  apply Nat.succ_inj
  rw [Nat.sub_succ, Nat.succ_pred]
  <;> auto [Nat.zero_lt_sub_of_lt]

section foldl_sim

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

end foldl_sim

section foldl_ind

variable (f : β → α → β)
variable (x₀ : β)
variable (M : β → Prop)

theorem foldl_ind (ar : Array α)
        (H' : M x₀)
        (H : ∀ x a, M x →  M (f x a)) :
  M (ar.foldl f x₀) := by
let SIM := λ x y => x = y ∧ M x
suffices SIM (foldl f x₀ ar 0 (size ar))
             (foldl f x₀ ar 0 (size ar)) by
  apply this.2
apply foldl_sim (SIM := SIM)
. constructor <;> auto
intros x x' a; rintro1 ⟨rfl, h₁⟩
auto

end foldl_ind

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

@[simp]
theorem toArray_toList {α} (ar : Array α) : ar.toList.toArray = ar := sorry

@[simp]
theorem toList_toArray {α} (l : List α) : l.toArray.toList = l := sorry

@[simp]
theorem size_toArray {α} (l : List α) : l.toArray.size = l.length := sorry

@[simp]
theorem length_toList {α} (ar : Array α) : ar.toList.length = ar.size := sorry

theorem foldl_toArray {α β : Type _} (f : β → α → β) (ar : List α) x₀ :
  n = ar.length →
  ar.toArray.foldl f x₀ 0 n = ar.foldl f x₀ := sorry

@[simp]
theorem foldl_toList {α β : Type _} (f : β → α → β) (ar : Array α) x₀ :
  ar.toList.foldl f x₀ = ar.foldl f x₀ := sorry

@[simp]
theorem map_mkEmpty {α β} (f : α → β) :
  f <$> mkEmpty n = mkEmpty n := rfl

@[simp]
theorem map_nil {α β} (f : α → β) :
  f <$> #[] = #[] := rfl

-- @[simp]
theorem toList_eq_data {α} (ar : Array α) :
  ar.toList = ar.data := by
cases ar with | mk ar =>
have : ar.length ≤ ar.length := by refl
simp [toList, size, foldr, foldrM, *]
split
focus
  simp only [size]
  generalize (Eq.mpr_prop (eq_true this) True.intro) = h
  let k := ar.length
  rw [← @List.drop_length _ ar]
  change List.length ar ≤ k at h
  revert h
  generalize ar.length = i; intros h
  induction i <;> simp [foldrM.fold]
  . refl
  next i IH =>
    have : ¬ (Nat.succ i == 0) = true := by
      intros h; cases h
    simp [*, get, List.cons_drop]
    done
focus
  suffices ar.length = 0 by
    simp at this; subst this
    refl
  apply Nat.le_antisymm _ (Nat.zero_le _)
  auto

theorem toList_inj (x y : Array α) :
  x.toList = y.toList → x = y := by
cases x; cases y
simp [toList_eq_data]; auto

@[simp]
theorem map_toArray {α β : Type _} (f : α → β) (l : List α) :
  f <$> l.toArray = (f <$> l).toArray := by
-- simp [List.toArray]
-- generalize Har : @mkEmpty α (List.length l) = ar
-- have := congrArg (Functor.map f) Har
-- simp at this; rw [this]; clear Har this
-- induction l generalizing ar
--  <;> simp [List.toArrayAux, *] <;> refl
sorry

theorem mkEmpty_eq_mkEmpty {α n} m :
  mkEmpty (α := α) n = mkEmpty m := rfl

@[simp]
theorem toList_mkEmpty {α n} :
  toList (@mkEmpty α n) = [] := sorry

@[simp]
theorem toList_push {α} (ar : Array α) (x) :
  toList (push ar x) = toList ar ++ [x] := sorry

end Array

namespace Subarray

def size (ar : Subarray α) : Nat := ar.stop - ar.start

def get (ar : Subarray α) (i : Nat) (Hi : i < ar.size) : α :=
have : ar.start + i < Array.size ar.as := by
  have := Nat.add_lt_of_lt_sub_l Hi
  apply Nat.lt_of_lt_of_le this ar.h₂
ar.as.get ⟨ar.start + i, this⟩

def get! [Inhabited α] (ar : Subarray α) (i : Nat) : α :=
ar.as.get! (ar.start + i)

def get? (ar : Subarray α) (i : Nat) : Option α :=
ar.as.get? (ar.start + i)

def empty (ar : Subarray α) : Bool := ar.start == ar.stop

@[simp]
theorem stop_popFront (ar : Subarray α) :
  ar.popFront.stop = ar.stop := by
simp [popFront]
byCases h : ar.start < ar.stop <;> simp [*]

@[simp]
theorem size_popFront (ar : Subarray α) :
  0 < ar.size →
  ar.popFront.size = ar.size - 1 := by
intros h
have h : ar.start < ar.stop := by simp [size] at h; assumption
simp [popFront, *, size, Nat.sub_succ]

@[simp]
theorem size_le_size_as (ar : Subarray α) :
  ar.size ≤ ar.as.size := sorry

def extract (ar : Subarray α) (i j : Nat) : Subarray α :=
  let start := min (ar.start + i) ar.stop
  let stop := min (max (ar.start + j) start) ar.stop
  have h₁ : start ≤ stop := by
    simp [Nat.le_min_iff]
    constructor
    focus
      apply Nat.le_max_r
      rewrite [Nat.le_min_iff]
      auto
    . admit
    -- . auto
  have h₂ : stop ≤ ar.as.size := by
    apply Nat.min_le_r; apply ar.h₂
  { as := ar.as,
    start := start,
    stop := stop,
    h₁ := h₁,
    h₂ := h₂ }

@[simp]
theorem extract_eq_self (ar : Subarray α) :
  ar.extract 0 ar.size = ar := by
cases ar; simp [extract, size, Nat.add_sub_assoc]
constructor
. auto
. apply Nat.le_max_l; simp [Nat.add_sub_cancel, *]; refl

theorem get_extract (ar : Subarray α) i p q h h' :
  (ar.extract p q).get i h = ar.get (p + i) h' := by
simp [extract, get]
-- have : min (ar.start + p) ar.stop + i = ar.start + (p + i) := sorry
have : ∀ i j, i = j → ar.as.get i = ar.as.get j := by
  intros _ _ h; subst h; refl
apply this; clear this; simp
have : min (ar.start + p) ar.stop = ar.start + p := by
  rw [Nat.min_eq_iff_le_l]
  apply Nat.le_of_lt
  apply Nat.add_lt_of_lt_sub_l
  apply Nat.lt_of_le_of_lt _ h'
  apply Nat.le_add_right
simp [this, Nat.add_assoc]

theorem popFront_extract (ar : Subarray α) p q
  (Hp : p < q)
  (Hq : q ≤ ar.size) :
  (ar.extract p q).popFront  = ar.extract p.succ q := by
have h₄ : p < ar.size := Nat.lt_of_lt_of_le Hp Hq
have H := Nat.add_lt_of_lt_sub_l h₄
simp [extract, popFront]
split <;> simp
next h =>
  have h₀ : min (ar.start + p) ar.stop = ar.start + p := by
    simp [Nat.le_of_lt, *]
  have h₁ : min (ar.start + p).succ ar.stop = (ar.start + p).succ := by
    simp [Nat.succ_le_of_lt, *]
  have h₂ : max q p = q := by
    simp [Nat.le_of_lt, *]
  have h₃ : max q p.succ = q := by
    simp [Nat.le_of_lt, *]; assumption
  simp [h₀, h₁, h₂] at h ⊢
  rw [← Nat.add_succ, Nat.max_add, h₃]
next h =>
  exfalso; apply h; clear h
  have : min (ar.start + p) ar.stop = (ar.start + p) := by
    simp; apply Nat.le_of_lt; assumption
  have : min (ar.start + q) ar.stop = (ar.start + q) := by
    simp [Nat.add_le_iff_l, ar.h₁]; assumption
  have : max q p = q := by
    simp; apply Nat.le_of_lt; assumption
  simp [*]
  apply Nat.add_lt_add_r; auto

theorem size_extract (ar : Subarray α) p q
  (h₀ : p ≤ q) (h₁ : q ≤ ar.size) :
  (ar.extract p q).size = q - p := by
have : min (ar.start + p) ar.stop = ar.start + p :=
  by simp [Nat.add_le_iff_l, ar.h₁]; trans _ <;> assumption
have : max (ar.start + q) ar.start = ar.start + q :=
  by simp [Nat.add_le_iff_r]; apply Nat.le_add_right
have : min (ar.start + q) ar.stop = ar.start + q :=
  by simp [Nat.add_le_iff_l, ar.h₁]; assumption
have : max q p = q := by simp [*]
simp [extract, size, *]
apply congrFun; apply congrArg
rw [Nat.add_comm, ← Nat.add_sub_assoc, Nat.sub_self, Nat.add_zero]
refl

attribute [simp] measure invImage InvImage Nat.lt_wfRel

syntax "prove_decr" : tactic
syntax "decr_step" : tactic
syntax "decr_finish" : tactic

macro_rules
| `(tactic| decr_finish) => `(tactic| assumption)

macro_rules
| `(tactic| decr_finish) => `(tactic| constructor)

macro_rules
| `(tactic| decr_step) => `(tactic| apply Nat.pred_lt; apply Nat.sub_ne_zero)

macro_rules
| `(tactic| decr_step) => `(tactic| apply Nat.sub_lt)

macro_rules
| `(tactic| prove_decr) =>
  `(tactic| { simp [*]; decr_step <;> decr_finish })

def takeWhileAux
            (p : α → Bool) (i : Nat) (ar : Subarray α) : Subarray α :=
if h : i < ar.size then
  if p $ ar.get i h then takeWhileAux p (Nat.succ i) ar
  else ar.extract 0 i
else ar.extract 0 i
termination_by' measure λ ⟨_, _, i, ar⟩ => ar.size - i
decreasing_by prove_decr

theorem takeWhileAux_eq (p : α → Bool) (ar : Subarray α) :
  takeWhileAux p i ar =
  if h : i < ar.size then
    if p $ ar.get i h then takeWhileAux p i.succ ar
    else ar.extract 0 i
  else ar.extract 0 i :=
WellFounded.fix_eq _ _ _

def takeWhile (p : α → Bool) (ar : Subarray α) : Subarray α :=
takeWhileAux p 0 ar

def spanAux (p : α → Bool) (i : Nat)
    (ar : Subarray α) : Subarray α × Subarray α :=
if h : i < ar.size then
  if p $ ar.get i h then spanAux p (Nat.succ i) ar
  else (ar.extract 0 i, ar.extract i ar.size)
else (ar.extract 0 i, ar.extract i ar.size)
termination_by' measure λ ⟨_, _, i, ar⟩ => ar.size - i
decreasing_by prove_decr

theorem spanAux_eq (p : α → Bool) (i : Nat) (ar : Subarray α) :
  spanAux p i ar =
  if h : i < ar.size then
    if p $ ar.get i h then spanAux p (Nat.succ i) ar
    else (ar.extract 0 i, ar.extract i ar.size)
  else (ar.extract 0 i, ar.extract i ar.size) :=
WellFounded.fix_eq _ _ _

def span (p : α → Bool) (ar : Subarray α) : Subarray α × Subarray α :=
spanAux p 0 ar

def dropWhile
            (p : α → Bool) (ar : Subarray α) : Subarray α :=
if h : 0 < ar.size then
  if p $ ar.get 0 h then dropWhile p ar.popFront
  else ar
else ar
termination_by' measure λ ⟨_, _, ar⟩ => ar.size
decreasing_by prove_decr

theorem dropWhile_eq (p : α → Bool) (ar : Subarray α) :
  dropWhile p ar =
  if h : 0 < ar.size then
    if p $ ar.get 0 h then dropWhile p ar.popFront
    else ar
  else ar :=
WellFounded.fix_eq _ _ _

theorem span_eq_takeWhile_dropWhile (p : α → Bool) (ar : Subarray α) :
  ar.span p = (ar.takeWhile p, ar.dropWhile p) := by
simp only [span, takeWhile]
suffices h : ∀ i,
    i ≤ ar.size →
    spanAux p i ar =
    (takeWhileAux p i <| ar,
     dropWhile p <| ar.extract i ar.size) by
  specialize h 0
  simp [h, *, Nat.zero_le]
intros i
generalize hk : (ar.size - i) = k
induction k using Nat.strong_ind generalizing i;
next ih =>
  rw [spanAux_eq, dropWhile_eq, takeWhileAux_eq]
  byCases h₀ : i < size ar <;> simp [*]
  focus
    subst hk
    have : i + 0 < ar.size := by simp [*]
    have h₅ : i ≤ ar.size := Nat.le_of_lt h₀
    have h₄ : ar.size ≤ ar.size := Nat.le_refl _
    have h : 0 < size (extract ar i (size ar)) :=
      by simp [size_extract, *]
    have h₃ : get ar (i + 0) this = get ar i h₀ :=
      by revert this; rw [Nat.add_zero]; intro; refl
    simp [get_extract (h' := this), h, h₃]
    split
    focus
      have : size ar ≤ size ar := by refl
      simp [popFront_extract, *]
      apply ih _ _ _ rfl h₀
      simp [Nat.sub_succ]
      apply Nat.pred_lt
      apply Nat.sub_ne_zero; assumption
    focus
      intros; refl
  focus
    intros h₁; subst hk
    have h₅ : ar.size ≤ i := Nat.le_of_not_lt h₀
    have h₅ := Nat.le_antisymm h₅ h₁
    subst h₅
    have h₄ : ar.size ≤ ar.size := Nat.le_refl _
    have h : ¬ 0 < size (extract ar (size ar) (size ar)) :=
      by simp [size_extract, *]
    simp [*]

end Subarray

namespace Array
variable (ar ar' : Array α)

@[simp]
theorem size_extract i j :
  (ar.extract i j).size = min ar.size (j - i) :=
sorry

@[simp]
theorem size_toSubarray i j :
  (ar.toSubarray i j).size = min ar.size (j - i) :=
sorry

theorem lt_size_toSubarray_implies_lt_size
        (h : k < (ar.toSubarray i j).size) :
  i + k < ar.size := sorry

@[simp]
theorem get_toSubarray  i j k h :
  (ar.toSubarray i j).get k h =
  ar.get ⟨i + k, lt_size_toSubarray_implies_lt_size _ h⟩ :=
sorry

@[simp]
def extractOffset : Fin (ar.extract i j).size → Fin ar.size
| ⟨n, h⟩ => ⟨i + n, sorry⟩

@[simp]
theorem get_extract i j k :
  (ar.extract i j).get k =
  ar.get (extractOffset _ k) :=
sorry

@[simp]
theorem get_eq_iff_get?_eq i h x :
  ar.get ⟨i, h⟩ = x ↔
  ar.get? i = some x :=
sorry

@[simp]
theorem some_get_eq_get? i h :
  some (ar.get ⟨i, h⟩) = ar.get? i :=
sorry

@[simp]
theorem size_append (ar₀ ar₁ : Array α) :
  (ar₀ ++ ar₁).size = ar₀.size + ar₁.size :=
sorry

theorem toArray_append (x y : List α) :
  (x ++ y).toArray = x.toArray ++ y.toArray :=
sorry

@[simp]
theorem push_append a (x y : Array α) :
  (x ++ y).push a = x ++ y.push a := sorry

@[simp]
theorem nil_appendList (a : List α) :
  #[].appendList a = a.toArray := sorry

theorem appendList_eq (x : Array α) (y : List α) :
  x.appendList y = x ++ y.toArray := sorry

theorem toList_append (x y : Array α) :
  toList (x ++ y) = x.toList ++ y.toList := sorry

-- #exit
-- @[simp]
-- theorem map_push {α β} (f : α → β) xs x :
--   f <$> Array.push xs x = Array.push (f <$> xs) (f x) := by
-- cases xs; simp [push, (.<$>.), map, mapM]

@[simp]
theorem append_nil (xs : Array α) :
  xs ++ #[] = xs := sorry

@[simp]
theorem nil_append (xs : Array α) :
  #[] ++ xs = xs := sorry

theorem append_assoc (xs ys zs : Array α) :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
apply toList_inj; simp [toList_append, List.append_assoc]

-- theorem toList_appendList (x : Array α) y :
--   toList (x.appendList y) = x.toList ++ y := by
-- let SIM {α} (x : Array α) (z : List α) := toList x = z ++ y
-- refine' Array.foldl_sim (SIM := SIM) (ar := x)
--   (f := Array.push) _ _ _ _ _ _

end Array

namespace Util

unsafe def isSharedUnsafe (x : @& α) : Bool := true

@[inline]
unsafe def withIsSharedUnsafe (x : α) (f : Bool → α → β)
           (h : f true x = f false x) : β :=
f (isSharedUnsafe x) x

@[implementedBy withIsSharedUnsafe]
def withIsShared (x : α) (f : Bool → α → β)
           (h : f true x = f false x) : β := f true x

theorem withIsShared_if_true (x : α) (f : Bool → α → β) h :
  withIsShared x f h = f true x := rfl

theorem withIsShared_if_false (x : α) (f : Bool → α → β) h :
  withIsShared x f h = f false x := h

end Util

def SubarrayOfSize (n : Nat) (α) :=
{ x : Subarray α // x.size = n }

namespace SubarrayOfSize

def get {n α} (ar : SubarrayOfSize n α)
  (i : Fin n) : α :=
ar.val.get i.1 <| ar.2.symm ▸ i.2

def toSubarray_idx (ar : Subarray α) : Fin ar.size → Fin ar.as.size
| ⟨i, h⟩ => ⟨i, sorry⟩

private def subarray_set (ar : Subarray α) (i : Fin ar.size)
            (x : α) : Subarray α where
  as := ar.as.set (toSubarray_idx _ i) x
  start := ar.start
  stop := ar.stop
  h₁ := ar.h₁
  h₂ := by simp [ar.h₂]

private theorem size_subarray_set (ar : Subarray α) i x :
  (subarray_set ar i x).size = ar.size := rfl

def set {n α} (ar : SubarrayOfSize n α)
  (i : Fin n) (a : α) : SubarrayOfSize n α :=
⟨ subarray_set ar.val (ar.2.symm ▸ i) a,
  by simp [size_subarray_set, ar.2]⟩

def get? {n α} (ar : SubarrayOfSize n α)
  (i : Nat) : Option α :=
ar.val.get? i

variable (ar : SubarrayOfSize n α)

@[simp]
theorem get_set i j x :
  (ar.set i x).get j = if i = j then x else ar.get j :=
sorry

@[simp]
theorem get_eq_iff_get?_eq  i h x :
  ar.get ⟨i, h⟩ = x ↔
  ar.get? i = some x :=
sorry

@[simp]
theorem some_get_eq_get? i h :
  some (ar.get ⟨i, h⟩) = ar.get? i :=
sorry

end SubarrayOfSize

def Subarray.Eqv {α} (n : Nat)
  (ar₀ ar₁ : SubarrayOfSize n α) : Prop :=
∀ i, ar₀.get i = ar₁.get i

theorem Subarray.Eqv.apply {α} (n : Nat)
        (ar₀ ar₁ : SubarrayOfSize n α)
        (h : Subarray.Eqv n ar₀ ar₁):
  ∀ i, i < n → ar₀.get? i = ar₁.get? i :=
by intros;
   rw [← SubarrayOfSize.some_get_eq_get?,
       ← SubarrayOfSize.some_get_eq_get?]
   <;> try assumption
   apply congrArg; apply h

def SubarrayQ (α) := Σ n, Quot <| @Subarray.Eqv α n

namespace Option

theorem some_inj {x y : α} (h : some x = some y) : x = y :=
by cases h; refl

end Option


namespace SubarrayQ

def ofSubarray (ar : Subarray α) : SubarrayQ α :=
⟨ar.size, Quot.mk _ ⟨ar, rfl⟩⟩

def size (ar : SubarrayQ α) := ar.1

def get : (ar : SubarrayQ α) → Fin ar.size → α
| ⟨n, ar⟩ => Quot.liftOn ar
  (λ ar (i : Fin n) => ar.get i) $ by
    { simp; intros a b h; apply funext; intros i;
      simp only [SubarrayOfSize.some_get_eq_get?]
      auto }

section Subarray
variable (ar : Subarray α)

@[simp]
theorem size_ofSubarray (ar : Subarray α) :
  size (ofSubarray ar) = ar.size :=
sorry

end Subarray

theorem ext (ar₀ ar₁ : SubarrayQ α)
        (h₀ : ar₀.size = ar₁.size)
        (h₁ : ∀ i h₀ h₁, ar₀.get ⟨i, h₀⟩ = ar₁.get ⟨i, h₁⟩) :
  ar₀ = ar₁ :=
sorry

@[simp]
theorem get_ofSubarray (ar : Subarray α) i h :
  (ofSubarray ar).get ⟨i,h⟩ = ar.get i h :=
sorry

def unshare : SubarrayQ α → SubarrayQ α
| ⟨n, ar⟩ =>
Quot.liftOn ar
  (λ ar =>
    let ⟨ar, i, j, _, _ ⟩ := ar.1
    Util.withIsShared ar
      (λ shared ar =>
        if shared
          then ofSubarray (ar.extract i j).toSubarray
          else ofSubarray ar[i:j])
      (by simp; apply ext <;> simp))
  (by simp [Util.withIsShared_if_false]
      intros a b h; apply ext <;> simp [a.2]
      focus
        change (a.1.3 - a.1.2) with a.1.size
        change (b.1.3 - b.1.2) with b.1.size
        simp [Nat.min_eq_iff_le_r |>.2]
        simp [a.2, b.2]
        done
      focus
        intros; apply h.apply
        rw [← a.2]
        simp at *
        auto )

@[simp]
theorem size_unshare (ar : SubarrayQ α) :
  ar.unshare.size = ar.size := sorry

def set (ar : SubarrayQ α) : Fin ar.size → α → SubarrayQ α :=
suffices Fin ar.unshare.size → α → SubarrayQ α
  by simp at this; assumption
match ar.unshare with
| ⟨n, ar⟩ => λ i : Fin n =>
Quot.liftOn ar
  (λ ar a => ⟨n, Quot.mk _ $ ar.set i a⟩)
  (by intros a b h; apply funext; intros x; simp;
      apply congrArg; apply Quot.sound; intro i;
      simp; split <;> auto )

end SubarrayQ

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
⟨ b₀.cells.zipWith b₁.cells f, by simp [Buffer.Hsize] ⟩

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
