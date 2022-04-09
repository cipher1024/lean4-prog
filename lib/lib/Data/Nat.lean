
import Lib.Logic.Classical
import Lib.Tactic

namespace Nat

attribute [auto] Nat.le_of_lt Nat.le_add_right Nat.zero_le
attribute [auto] Nat.le_add_left Nat.le_add_right
attribute [auto] Nat.add_le_add_right Nat.add_le_add_left
attribute [simp] Nat.add_succ Nat.succ_sub_succ Nat.lt_succ_self
attribute [simp] Nat.pow_succ Nat.pow_zero
attribute [simp] Nat.add_sub_cancel_left Nat.add_sub_of_le
attribute [simp] Nat.add_sub_add_left Nat.add_sub_add_right

theorem succ_inj {m n : Nat} (h : m.succ = n.succ) : m = n :=
by cases h; refl

theorem ne_symm {x y : Nat} : x ≠ y → y ≠ x :=
by intros h h'; subst h'; apply h; rfl

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

@[auto]
theorem le_add_of_le_l {m n k : Nat}
        (h : m ≤ n) :
  m ≤ n + k :=
by trans n <;> auto

@[auto]
theorem le_add_of_le_r {m n k : Nat}
        (h : m ≤ k) :
  m ≤ n + k :=
by trans k <;> auto

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
. simp [Nat.sub,sub_succ, *]

theorem strong_ind {P : Nat → Prop} :
  (∀ x, (∀ y, y < x → P y) → P x) → ∀ a, P a :=
by intros h x; apply Nat.lt_wfRel.wf.induction (C := P) x h

theorem le_of_not_lt {x y : Nat}
        (h : ¬ y < x) :
  x ≤ y := by
cases Nat.lt_or_ge y x <;> auto

@[auto]
theorem not_lt_of_le {x y : Nat}
        (h : y ≤ x) :
  ¬ x < y := by
intros h'
apply Nat.not_le_of_gt h' h

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
simp [eq_iff_forall_le_iff]; auto with 6

theorem min_comm : min x y = min y x := by
simp [eq_iff_forall_ge_iff]; auto with 6

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
by_cases h : p ≤ z
. simp [Nat.add_le_iff_l, *]
focus
  have : ∀ q, ¬ p + q ≤ z := by
    intros q h'; apply h; clear h
    trans _; case second => assumption
    auto
  simp [*]
end max_min

end Nat

namespace Nat

theorem lt_iff_not_le {x y : Nat} :
  x < y ↔ ¬ y ≤ x :=
by auto [Nat.gt_of_not_le, Nat.not_le_of_gt]

theorem le_iff_not_lt {x y : Nat} :
  x ≤ y ↔ ¬ y < x :=
by auto [Nat.le_of_not_gt, Nat.not_lt_of_le]

@[auto]
theorem div_gcd_self_l : d / gcd n d > 0 :=
sorry

theorem gcd_mul p q n : gcd p q * n = gcd (p * n) (q * n) :=
sorry

theorem mul_inj (h : n > 0) : p * n = q * n → p = q :=
sorry

def divides (p q : Nat) :=
∃ k, p * k = q

infix:65 " ∣ " => divides

@[simp]
theorem div_mul_self (h : p ∣ q) :
  q / p * p = q := sorry

@[simp]
theorem gcd_divides_l : gcd p q ∣ p :=
sorry

@[simp]
theorem gcd_divides_r : gcd p q ∣ q :=
sorry

theorem sub_lt_of_lt_add {x y : Nat} (h₀ : y ≤ x) :
  x < z + y →
  x - y < z := by
intros h
apply Nat.gt_of_not_le
intros h'
apply Nat.not_le_of_gt h; clear h
rw [add_le_iff_r]
<;> auto

theorem sub_add_self {a b : Nat} (h : b ≤ a) :
  (a - b) + b = a := by
rw [Nat.add_comm, ← Nat.add_sub_assoc, Nat.add_sub_self_left]
<;> assumption

theorem le_add_of_sub_le_l {m n k : Nat} :
  n - k ≤ m → n ≤ k + m := by
rw [le_iff_not_lt, le_iff_not_lt]
intros h h'
apply h; clear h
apply Nat.lt_of_le_of_lt (m := (k + m) - k)
next =>
  rw [add_sub_self_left]; refl
next =>
  apply sub_lt_of_lt_add; auto
  rw [Nat.sub_add_self]; auto
  trans k + m <;> auto

@[simp]
theorem add_sub_cancel_l {x y : Nat} :
  x + y - y = x := by
rw [eq_iff_forall_ge_iff]; intro z
rw [← add_le_iff_r]
constructor
focus
  apply Nat.le_of_add_le_add_right
focus
  auto
focus
  apply Nat.le_add_left

theorem succ_le_iff {x y : Nat} (h : 0 < y) :
  succ x ≤ y ↔ x ≤ pred y := by
induction y
. cases h
. simp [pred]

section div

theorem div_sub_self {x y : Nat} :
  (x - y) / y = pred (x / y) := by
rw [div_eq x y]; split
. refl
next h =>
  have : ¬ (0 < y ∧ y ≤ x - y) := by
    intros h'; cases h'
    apply h; clear h
    constructor; assumption
    trans (x - y)
    <;> auto [Nat.sub_le]
  rw [div_eq]; simp [*]

theorem mul_le_iff_le_div {x y k : Nat} (h : 1 ≤ k) :
  x*k ≤ y ↔ x ≤ y / k := by
induction x generalizing y with
| zero => simp [zero_le]
| succ x =>
  simp [succ_mul]
  have Hy := div_eq y k
  revert Hy; split <;> intro Hy
  next h =>
    cases h
    have : 0 < y / k := by
      simp [Hy, zero_lt_succ]
    clear Hy
    simp [succ_le_iff, add_le_iff_r, div_sub_self, *]
    done
  next h =>
    have h : ¬ k ≤ y := by
      intro h₀; apply h; auto
    simp [Hy, Classical.iff_iff_and_or_and]
    next =>
      intros h'; apply h; clear h
      trans x * k + k <;>  auto [Nat.le_add_left]

theorem div_lt {x k : Nat} (h : k > 1) (h' : 0 < x) :
  x / k < x := by
rw [lt_iff_not_le, ← mul_le_iff_le_div]
focus
  intros h
  have h' : x * k ≤ x * 1 := sorry
  -- have := mul_inj _ h'
  admit
admit

theorem div_le_div {x y k : Nat} (h : x ≤ y) :
  x / k ≤ y / k :=
sorry

end div

section pow

@[simp]
theorem one_pow {x : Nat} : 1^x = 1 := by
induction x <;> simp; assumption

@[auto]
theorem one_le_pow {x y : Nat} (h : 1 ≤ x) :
  1 ≤ x^y := by
suffices 1^y ≤ x^y by
  simp [one_pow] at this; auto
auto [pow_le_pow_of_le_left]

end pow

section log2

theorem log2_def n :
  log2 n =
  if h : n ≥ 2 then log2 (n / 2) + 1 else 0 :=
WellFounded.fix_eq _ _ _

@[simp]
theorem log2_one : log2 1 = 0 := by
have h₀ : ¬ 2 ≤ 1 :=
  by intros h; cases h with
     | step h  => apply Nat.not_succ_le_zero _ h
rw [log2_def]; simp [*]

@[simp]
theorem log2_2 : log2 2 = 1 := by
have h₀ : 2 ≤ 2 := by refl
rw [log2_def]; simp [*]

theorem log2_div_2 {x : Nat} : log2 (x / 2) = log2 x - 1 := by
rw [log2_def x]
split
. rw [add_sub_cancel_l]
next h' =>
have : ¬ 2 ≤ x / 2 := by
  intros h₀; apply h'
  admit
  -- trans x / 2 <;> try auto
  -- apply Nat.le_of_lt
  -- apply div_lt
  -- . repeat constructor
  -- apply gt_of_not_le
  -- intro h; have h := Nat.le_antisymm h (zero_le _)
  -- subst h; cases h₀
rw [log2_def]; simp [*]

theorem log2_le_log2 {x y : Nat} (h : x ≤ y) :
  log2 x ≤ log2 y := by
induction x using Nat.strong_ind generalizing y;
next x ih =>
  rw [log2_def x,log2_def y]
  split
  next h₀ =>
    have : 2 ≤ y := by
      trans x <;> assumption
    simp [*]; apply ih
    focus
      have h₁ : 0 < 2 := by repeat constructor
      have h₂ : 1 < 2 := by repeat constructor
      apply Nat.div_lt h₂
      apply Nat.lt_of_lt_of_le h₁ h₀
    focus
      auto [Nat.div_le_div]
  focus auto

theorem pow_le_iff_le_log {x y : Nat} (h : 1 ≤ y) :
  2^x ≤ y ↔ x ≤ log2 y := by
induction x generalizing y;
. simp [*, Nat.zero_le]
by_cases h : 1 ≤ y / 2
focus
  have h' : 1 ≤ log2 y := by
    rw [← mul_le_iff_le_div] at h
    have h := log2_le_log2 h
    simp at h; all_goals auto
  simp [*, Nat.zero_le, mul_le_iff_le_div, log2_div_2, ← add_le_iff_r]
next n ih _ =>
  have h' : y = 1 := by
    admit
    -- rw [← mul_le_iff_le_div] at h
    -- apply Nat.le_antisymm
    -- all_goals auto
  have h'' : succ n ≤ 0 ↔ False :=
    by auto [Nat.not_succ_le_zero]
  subst y; simp [mul_le_iff_le_div, *]
  apply Nat.not_le_of_gt
  change 1 /2 with 0
  auto [pos_pow_of_pos]

end log2

end Nat
