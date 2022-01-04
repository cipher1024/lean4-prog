
import Lib.Tactic
import Lib.Classical

namespace Nat

attribute [auto] Nat.le_of_lt Nat.le_add_right Nat.zero_le
attribute [simp] Nat.add_succ Nat.succ_sub_succ Nat.lt_succ_self

@[simp]
theorem zero_sub (n : Nat) : 0 - n = 0 := by
  induction n <;> simp [sub_succ, *]

theorem add_lt_of_lt_sub_r {m n k : Nat} :
  m < n - k → m + k < n := by
induction k generalizing n with
| zero =>
  simp; apply id
| succ k ih =>
  simp
  cases n <;> simp
  { intros h; cases h }
  simp [succ_sub_succ, add_succ]
  intros h; apply succ_lt_succ
  apply ih; assumption

theorem add_succ_eq_succ_add (m n : Nat) :
  m + succ n = succ m + n := by
simp [Nat.add_succ, Nat.succ_add]

theorem add_lt_of_lt_sub_l {m n k : Nat} :
  m < n - k → k + m < n := by
rw [Nat.add_comm]; apply add_lt_of_lt_sub_r

-- theorem add_le_of_le_sub_r {m n k : Nat} :
--   m ≤ n - k → m + k ≤ n := by
-- induction k generalizing m n with
-- | zero =>
--   simp; apply id
-- | succ k ih =>
--   cases n
--   simp [Nat.add_succ_eq_succ_add]
--   intro h; apply ih
--   have h' : n - succ k ≤ n - k := sorry

--   -- apply Nat.succ_le_
--   -- have h := Nat.succ_le_succ h
--   -- cases n <;> simp [Nat.add_succ_eq_succ_add, Nat.succ_sub_succ]
--   -- . intros h; apply ih
--   -- . apply ih
--   -- { intros h; cases h }
--   -- simp [succ_sub_succ, add_succ]
--   -- intros h; apply succ_lt_succ
--   -- apply ih; assumption

-- theorem add_le_of_le_sub_l {m n k : Nat} :
--   m ≤ n - k → k + m ≤ n := by
-- rw [Nat.add_comm]; apply add_le_of_le_sub_r

@[simp]
theorem succ_lt_succ_iff {n m : Nat} : succ n < succ m ↔ n < m :=
⟨ lt_of_succ_lt_succ, succ_lt_succ ⟩

@[simp]
theorem zero_lt_sub_iff_lt {x y : Nat} :
  0 < y - x ↔ x < y := by
induction x generalizing y <;>
  cases y <;> simp [*]
intros h; cases h

theorem sub_ne_zero {x y : Nat} :
  x < y → y - x ≠ 0 := by
intros h
have h' : 0 < y - x := by simp [*]
intros h''; rewrite [h''] at h'; clear h''
apply Nat.lt_irrefl _ h'

@[simp]
theorem sub_add_assoc {x y z : Nat} :
  x - (y + z) = x - y - z :=
by induction z <;> simp [Nat.sub_succ, *]

theorem add_sub_assoc {x y z : Nat} :
  z ≤ y →
  x + (y - z) = x + y - z := by
  intro h
  induction y generalizing z;
  focus
    cases h
    simp [Nat.zero_sub, Nat.sub_zero]
  next y ih =>
    simp [Nat.succ_add, *]
    cases z with
    | zero => simp [Nat.succ_sub_succ] at *
    | succ z =>
      have h := Nat.le_of_succ_le_succ h
      simp [ih, h]

@[simp]
theorem add_sub_cancel {x y : Nat} :
  x ≤ y → x + (y - x) = y := by
  intros h; simp [add_sub_assoc, *]
  rw [Nat.add_comm, ← add_sub_assoc, Nat.sub_self, Nat.add_zero]
  refl

@[auto]
theorem le_of_not_gt {x y : Nat} (h : ¬ y < x) : x ≤ y := by
byContradiction h;
cases (Nat.lt_or_ge y x) <;> contradiction

theorem min_lt_min_l {x x' y y' : Nat}
  (Hx : x < x')
  (Hy : y < y') :
  min x y < min x' y' := by
simp [min]
split <;> split <;> try assumption
. apply Nat.lt_of_le_of_lt <;> assumption
next h₀ _ =>
  have h₀ : y < x := Nat.gt_of_not_le h₀
  apply Nat.lt_trans <;> assumption



theorem max_lt_max {x x' y y' : Nat}
  (Hx : x < x')
  (Hy : y < y') :
  max x y < max x' y' := by
simp [max]
split <;> split <;> try assumption
focus
  apply Nat.lt_of_lt_of_le Hx
  auto [Nat.le_of_not_gt]
focus
  trans y' <;> assumption

@[simp]
theorem succ_le_succ_iff {p q : Nat} :
  p.succ ≤ q.succ ↔ p ≤ q := by
constructor
. apply Nat.le_of_succ_le_succ
. apply Nat.succ_le_succ

theorem succ_le_iff_le_pred {p q : Nat}
  (h : 0 < q) :
  Nat.succ p ≤ q ↔ p ≤ Nat.pred q := by
induction q
focus cases h
focus
  simp [Nat.succ_le_succ, Nat.pred]

theorem pred_sub {p q} : Nat.pred p - q = Nat.pred (p - q) := by
simp [(.-.), Sub.sub]; induction q
. apply Nat.sub_zero
. simp [Nat.sub, *]

theorem add_le_iff_l {p q z : Nat}
  (Hq : z ≤ q) :
  z + p ≤ q ↔ p ≤ q - z := by
induction z generalizing q;
focus simp
next z ih =>
  have : 0 < q := by
    apply Nat.le_trans _ Hq
    apply Nat.succ_le_succ
    apply Nat.zero_le
  have : z ≤ Nat.pred q := by
    rw [← Nat.succ_le_iff_le_pred] <;> assumption
  simp [Nat.succ_add, Nat.sub_succ, Nat.succ_le_iff_le_pred, *, Nat.pred_sub]

theorem add_le_iff_r {p q z : Nat}
  (Hq : z ≤ q) :
  p + z ≤ q ↔ p ≤ q - z :=
by rw [Nat.add_comm]; simp [add_le_iff_l, *]

section max_min

variable {x y z : Nat}

theorem eq_iff_forall_le_iff :
  x = y ↔ ∀ z, x ≤ z ↔ y ≤ z := by
constructor <;> intros h
. subst h; intros; exact Iff.rfl
focus
  apply Nat.le_antisymm
  . rw [h]; refl
  . rw [← h]; refl

theorem eq_iff_forall_ge_iff :
  x = y ↔ ∀ z, z ≤ x ↔ z ≤ y := by
constructor <;> intros h
. subst h; intros; exact Iff.rfl
focus
  apply Nat.le_antisymm
  . rw [← h]; refl
  . rw [h]; refl

theorem le_iff_forall_le_implies :
  x ≤ y ↔ ∀ z, y ≤ z → x ≤ z := by
constructor <;> intros h
. intros z h₁; trans y <;> assumption
apply h <;> refl

theorem le_iff_forall_ge_implies :
  x ≤ y ↔ ∀ z, z ≤ x → z ≤ y := by
constructor <;> intros h
. intros z h₁; trans x <;> assumption
apply h <;> refl

@[simp]
theorem max_le_iff :
  max x y ≤ z ↔ x ≤ z ∧ y ≤ z := by
simp [max]; split
next h =>
  constructor <;> intros h'
  focus
    constructor <;> try assumption
    trans _
    . apply Nat.le_of_lt h
    . assumption
  focus
    cases h'; assumption
next h =>
  have : x ≤ y := by
    rewrite [← Classical.not_not (x ≤ y)]
    intros h'; apply h; apply gt_of_not_le h'
  constructor <;> intros h'
  focus
    constructor <;> try assumption
    trans _ <;> assumption
  focus
    cases h'; assumption

@[simp]
theorem le_min_iff :
  x ≤ min y z ↔ x ≤ y ∧ x ≤ z := by
simp [min]; split
next h =>
  constructor <;> intros h'
  focus
    constructor <;> try assumption
    trans _ <;> assumption
  focus
    cases h'; assumption
next h =>
  have : z ≤ y := by
    cases Nat.le_total z y <;> trivial
  constructor <;> intros h'
  focus
    constructor <;> try assumption
    trans _ <;> assumption
  focus
    cases h'; assumption

theorem max_comm : max x y = max y x := by
simp [eq_iff_forall_le_iff]; auto

theorem min_comm : min x y = min y x := by
simp [eq_iff_forall_ge_iff]; auto

theorem le_max_l : x ≤ y → x ≤ max y z := by
intros h
rewrite [le_iff_forall_le_implies]; intros z
rewrite [max_le_iff]; intros h; cases h
trans _ <;> assumption

theorem le_max_r : x ≤ z → x ≤ max y z := by
rw [max_comm]; apply le_max_l
-- intros h
-- rewrite [le_iff_forall_le_implies]; intros z
-- rewrite [max_le_iff]; intros h; cases h
-- trans _ <;> assumption

theorem lt_max_l : x < y → x < max y z := by
apply le_max_l

theorem lt_max_r : x < z → x < max y z := by
apply le_max_r

theorem add_lt_add_r : y < z → x + y < x + z := by
intros h
induction x <;> simp [*, succ_add]

theorem min_le_l : x ≤ z → min x y ≤ z := by
intros h
rewrite [le_iff_forall_ge_implies]; intros z
rewrite [le_min_iff]; intros h; cases h
trans x <;> assumption

theorem min_le_r : y ≤ z → min x y ≤ z := by
rw [min_comm]; apply min_le_l

@[auto] theorem self_le_max_l : x ≤ max x y := le_max_l $ by refl
@[auto] theorem self_le_max_r : y ≤ max x y := le_max_r $ by refl
@[auto] theorem min_le_self_l : min x y ≤ x := min_le_l $ by refl
@[auto] theorem min_le_self_r : min x y ≤ y := min_le_r $ by refl

@[simp] theorem min_eq_iff_le_l : min x y = x ↔ x ≤ y := by
  constructor <;> intros h
  . rw [← h]; auto
  focus
    apply Nat.le_antisymm
    . auto
    . simp; auto


@[simp] theorem min_eq_iff_le_r : min x y = y ↔ y ≤ x := by
  rw [min_comm, min_eq_iff_le_l]; refl

@[simp] theorem max_eq_iff_le_l : max x y = x ↔ y ≤ x := by
  constructor <;> intros h
  . rw [← h]; auto
  focus
    apply Nat.le_antisymm
    . simp; auto
    . auto

@[simp] theorem max_eq_iff_le_r : max x y = y ↔ x ≤ y := by
  rw [max_comm, max_eq_iff_le_l]; refl


@[simp]
theorem min_self : min x x = x := by
rw [min_eq_iff_le_r]; refl

@[simp]
theorem max_self : max x x = x := by
rw [max_eq_iff_le_r]; refl

@[simp]
theorem lt_min_iff :
  x < min y z ↔ x < y ∧ x < z := by
constructor
focus
  intros h; constructor
  . apply Nat.lt_of_lt_of_le h; auto
  . apply Nat.lt_of_lt_of_le h; auto
focus
  intros h; cases h with | intro h₀ h₁ =>
  rw [← min_self (x := x)]
  apply min_lt_min_l <;> assumption

@[simp]
theorem lt_max_iff :
  max x y < z ↔ x < z ∧ y < z := by
constructor
focus
  intros h; constructor
  <;> apply Nat.lt_of_le_of_lt _ h <;> auto
focus
  intros h; cases h with | intro h₀ h₁ =>
  rw [← max_self (x := z)]
  apply max_lt_max <;> assumption

@[simp]
theorem max_add {p q₀ q₁ : Nat} :
  max (p + q₀) (p + q₁) = p + max q₀ q₁ := by
simp [Nat.eq_iff_forall_le_iff]; intros z
byCases h : p ≤ z
. simp [Nat.add_le_iff_l, *]
focus
  have : ∀ q, ¬ p + q ≤ z := by
    intros q h'; apply h; clear h
    trans _; case second => assumption
    auto
  simp [*]
end max_min

end Nat
