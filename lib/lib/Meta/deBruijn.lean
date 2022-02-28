
import Lib.Data.Nat
import Lib.Data.Ordering
import Lib.Data.List.Basic
import Lib.Meta.DeclGraph
import Lib.Meta.Opaque
import Lib.Order.Basic

namespace Fin
open Nat
@[simp]
protected def succ {n} : Fin n → Fin (succ n)
| ⟨i,h⟩ => ⟨i.succ, Nat.succ_lt_succ h⟩

def last : Fin (succ n) := ⟨n, Nat.lt_succ_self _⟩

@[simp]
def widen {n} : Fin n → Fin (succ n)
| ⟨i,h⟩ => ⟨i, Nat.lt_succ_of_le <| Nat.le_of_lt h⟩

def split {m n} : Fin (m + n) → Fin m ⊕ Fin n
| ⟨i, h⟩ =>
  if h' : i < m
  then Sum.inl ⟨i, h'⟩
  else
    have : i - m < n :=
      Nat.sub_lt_of_lt_add
        (Nat.le_of_not_gt h') (Nat.add_comm n m ▸ h)
    Sum.inr ⟨i - m, this⟩

def cast (h : m = n) : Fin m → Fin n
| ⟨i, h'⟩ => ⟨i, h ▸ h'⟩

def cutl : (i : Fin (m + n)) → i.val < m → Fin m
| ⟨i, h⟩, h' => ⟨i, h'⟩

def cutr : (i : Fin (m + n)) → ¬ i.val < m → Fin n
| ⟨i, h⟩, h' =>
  have : i - m < n :=
    Nat.sub_lt_of_lt_add
      (Nat.le_of_not_gt h') (Nat.add_comm n m ▸ h)
  ⟨i - m, this⟩

def cutl' : (i : Fin (n + m)) → i.val < m → Fin m
| ⟨i, h⟩, h' => ⟨i, h'⟩

def cutr' : (i : Fin (n + m)) → ¬ i.val < m → Fin n
| ⟨i, h⟩, h' =>
  have : i - m < n :=
    Nat.sub_lt_of_lt_add
      (Nat.le_of_not_gt h') (Nat.add_comm n m ▸ h)
  ⟨i - m, this⟩

@[simp]
theorem val_last :
  (@Fin.last n).val = n := rfl

@[simp]
theorem val_cast (h : m = n) (i : Fin m) :
  (i.cast h).val = i := rfl

@[simp]
theorem val_cutl (i : Fin (m + n)) h :
  (i.cutl h).val = i.val := rfl

@[simp]
theorem val_cutr (i : Fin (m + n)) h :
  (i.cutr h).val = i.val - m := rfl

@[simp]
theorem val_cutl' (i : Fin (m + n)) h :
  (i.cutl' h).val = i.val := rfl

@[simp]
theorem val_cutr' (i : Fin (m + n)) h :
  (i.cutr' h).val = i.val - n := rfl

theorem val_inj {x y : Fin n} (h : x.val = y.val) : x = y :=
by cases x; cases y; cases h; refl

end Fin

namespace List

theorem get_eq_of_eq_0 {xs : List α} (i : Fin _)
        (h : i.val = 0) :
  (x :: xs).get i = x := by
cases i; cases h
simp [List.get]

end List

namespace Bool

-- @[simp]
-- theorem and_eq_true : (x && y) = true ↔ x = true ∧ y = true := by
-- cases x <;> cases y <;> simp

@[simp]
theorem decide_eq_true [H : Decidable p] :
  decide p = true ↔ p := by
cases H <;> simp [decide] <;> assumption

end Bool


namespace Lean
namespace Name

-- @[simp]
-- theorem beq_anonymous :
--   (anonymous == anonymous) = true := rfl

-- @[simp]
-- theorem beq_num :
--   (num p n h == num p' n' h') = true ↔
--   (p == p') = true ∧ n = n' :=
-- by simp [BEq.beq, Name.beq] <;> auto

-- @[simp]
-- theorem beq_str :
--   (str p n h == str p' n' h') = true ↔
--   (p == p') = true ∧ n = n' ∧ h = h' :=
-- by simp [BEq.beq, Name.beq] <;> auto

-- theorem beq_iff_eq {n n' : Name} :
--   n == n' ↔ n = n' := by
-- induction n generalizing n'
-- <;> cases n'
-- <;> next =>
--   constructor <;> simp [*] <;> intro h
--   <;> try (cases h) <;> try auto

-- #exit
instance : DecidableEq Name
| n, n' =>
  withPtrEqDecEq n n' λ () =>
    match n, n' with
    | anonymous, anonymous => isTrue rfl
    | str p n h, str p' n' h' =>
      have hh := (inferInstanceAs (Decidable (h = h')))
      have hn := (inferInstanceAs (Decidable (n = n')))
      have hp := instDecidableEqName p p'
      have h := @instDecidableAnd _ _ hh (@instDecidableAnd _ _ hn hp)
      @Decidable.congr _ _ h <| by
        constructor <;> intro h
        next =>
          repeat
            first
            | rfl
            | apply congr
          all_goals auto
        next => cases h; auto
    | num p n h, num p' n' h' =>
      have hh := (inferInstanceAs (Decidable (h = h')))
      have hn := (inferInstanceAs (Decidable (n = n')))
      have hp := instDecidableEqName p p'
      have h := @instDecidableAnd _ _ hh (@instDecidableAnd _ _ hn hp)
      @Decidable.congr _ _ h <| by
        constructor <;> intro h
        next =>
          repeat
            first
            | rfl
            | apply congr
          all_goals auto
        next => cases h; auto
    | num _ _ _, str _ _ _ => isFalse λ h => by cases h
    | num _ _ _, anonymous => isFalse λ h => by cases h
    | str _ _ _, num _ _ _ => isFalse λ h => by cases h
    | str _ _ _, anonymous => isFalse λ h => by cases h
    | anonymous, num _ _ _ => isFalse λ h => by cases h
    | anonymous, str _ _ _ => isFalse λ h => by cases h

end Name
end Lean


inductive Typ : Type
| nat | bool | arrow (t₀ t₁ : Typ)

open Nat
open Lean (Name)

inductive Term' : Nat → Type
| bvar {n} : Fin n → Term' n
| fvar {n} : Name → Term' n
| plus {n} (t₀ t₁ : Term' n) : Term' n
| ite {n} (c t₀ t₁ : Term' n) : Term' n
| app {n} (t₀ t₁ : Term' n) : Term' n
| lam {n} : Typ → Term' (succ n) → Term' n

namespace Term'

def bump (k : Nat) : Term' n → Term' (succ n)
| bvar i =>
  if k ≤ i.val then bvar i.succ else bvar <| i.widen
| fvar v => fvar v
| plus t₀ t₁ => plus (bump k t₀) (bump k t₁)
| Term'.ite c t₀ t₁ => ite (bump k c) (bump k t₀) (bump k t₁)
| app t₀ t₁ => app (bump k t₀) (bump k t₁)
| lam T t => lam T (bump k.succ t)

def subst (v : Name) (e : Term' n) : Term' n → Term' n
| bvar i => bvar i
| fvar v' =>
  if v == v' then e else fvar v'
| plus t₀ t₁ => plus (subst v e t₀) (subst v e t₁)
| Term'.ite c t₀ t₁ =>
  ite (subst v e c) (subst v e t₀) (subst v e t₁)
| app t₀ t₁ => app (subst v e t₀) (subst v e t₁)
| lam T t' => lam T (subst v (bump 0 e) t')

-- #print _sizeOf_inst
-- #pred sizeOf

-- inductive Subterm : ((n : Nat) × Term' n) → ((n : Nat) × Term' n) → Prop
-- | plus₀ {n} {t₀ t₁ : Term' n} : Subterm ⟨n, t₀⟩ ⟨n, plus t₀ t₁⟩
-- | plus₁ {n} {t₀ t₁ : Term' n} : Subterm ⟨n, t₁⟩ ⟨n, plus t₀ t₁⟩
-- | app₀ {n} {t₀ t₁ : Term' n} : Subterm ⟨n, t₀⟩ ⟨n, app t₀ t₁⟩
-- | app₁ {n} {t₀ t₁ : Term' n} : Subterm ⟨n, t₁⟩ ⟨n, app t₀ t₁⟩
-- | itec {n} {c t₀ t₁ : Term' n} : Subterm ⟨n, c⟩ ⟨n, Term'.ite c t₀ t₁⟩
-- | ite₀ {n} {c t₀ t₁ : Term' n} : Subterm ⟨n, t₀⟩ ⟨n, Term'.ite c t₀ t₁⟩
-- | ite₁ {n} {c t₀ t₁ : Term' n} : Subterm ⟨n, t₁⟩ ⟨n, Term'.ite c t₀ t₁⟩
-- | lam {n} {T} {t : Term' _} : Subterm ⟨_, t⟩ ⟨n, lam T t⟩

-- @[simp]
def height : Term' n → Nat
| bvar _ => 0
| fvar _ => 0
-- | plus t₀ t₁ => 1 + height t₀ + height t₁
| plus t₀ t₁ => height t₀ + height t₁ + 1
| app t₀ t₁ => height t₀ + height t₁ + 1
| Term'.ite c t₀ t₁ => height c + height t₀ + height t₁ + 1
| lam T t => height t + 1

-- namespace sizeOf

-- variable {c t₀ t₁ : Term' n}
-- variable (i : Fin 0)
-- -- #eval sizeOf (@bvar 1 ⟨0, Nat.zero_lt_one⟩)
-- #reduce sizeOf (bvar i)

-- theorem _eq_1  : sizeOf (bvar i) = 1 :=
-- show n.succ = _ from _

-- end sizeOf


-- set_option pp.explicit true in
-- #check @sizeOf (Term' _) _
-- #succ Term'
-- #exit

-- inductive A := | a

-- def termWf : WellFoundedRelation ((n : Nat) × Term' n) where
--   rel := Subterm
--   wf := by
--     constructor; intro a; cases a
--     next n t =>
--     induction t <;> constructor
--     <;> intro a <;> cases a <;> intro h
--     <;> cases h <;> assumption

-- #check measure
-- #check Nat.le_add_left
attribute [scoped auto] Nat.le_add_left Nat.le_add_right Nat.succ_le_succ

-- open Ordering in
-- def inst {n} (k : Fin (succ n)) (e : Term' n) : Term' (succ n) → Term' n
-- | bvar i =>
--   match compare i.val k.val, rfl : (o : Ordering) → compare i.val k = o → _ with
--   | eq, h => e
--   | lt, h =>
--     -- have h₀ : i.val < k.val := sorry
--     have h₀ : i.val < k.val := by
--       simp at h; assumption
--     have h₁ : k.val ≤ n := Nat.le_of_succ_le_succ k.isLt
--     bvar ⟨i.val, Nat.lt_of_lt_of_le h₀ h₁⟩
--   | gt, h =>
--     -- have : 1 ≤ i.val := sorry
--     have : 1 ≤ i.val := by
--       simp at h; trans _ </> assumption
--       auto
--     have : i.val - 1 < n := Nat.sub_lt_of_lt_add this i.isLt
--     bvar ⟨i.val - 1,  this⟩
-- | fvar v => fvar v
-- | plus t₀ t₁ =>
--        have : height t₀ < height (plus t₀ t₁) :=
--          by simp [height];
--             apply Nat.succ_le_succ
--             apply Nat.le_add_right
--          -- by simp [height]; auto
--        have : height t₁ < height (plus t₀ t₁) :=
--          by simp [height];
--             apply Nat.succ_le_succ
--             apply Nat.le_add_left
--             -- apply Nat.le_add_of_le_r
--          --    -- apply Nat.le_add_right
--          -- by simp [height]; auto
--        plus (inst k e t₀) (inst k e t₁)
-- | Term'.ite c t₀ t₁ =>
--        have : height c  < height (ite c t₀ t₁) :=
--          by simp [height];
--             apply Nat.succ_le_succ
--             apply Nat.le_add_of_le_l
--          --    -- apply Nat.le_add_right
--             apply Nat.le_add_right
--        have : height t₀ < height (ite c t₀ t₁) :=
--          by simp [height];
--             apply Nat.succ_le_succ
--             apply Nat.le_add_of_le_l
--          --    -- apply Nat.le_add_right
--             apply Nat.le_add_left
--          --    -- auto with 10
--        have : height t₁ < height (ite c t₀ t₁) :=
--          by simp [height];
--             apply Nat.succ_le_succ
--             -- apply Nat.le_add_of_le_l
--             apply Nat.le_add_left
--        ite (inst k e c) (inst k e t₀) (inst k e t₁)
-- | app t₀ t₁ =>
--        have : height t₀ < height (app t₀ t₁) :=
--          by simp [height]
--             apply Nat.succ_le_succ
--             apply Nat.le_add_right
--          -- by simp [height]; auto
--        have : height t₁ < height (app t₀ t₁) :=
--          by simp [height]
--             apply Nat.succ_le_succ
--             apply Nat.le_add_left
--          --    -- auto with 17
--        app (inst k e t₀) (inst k e t₁)
-- | lam T t' =>
--   -- have : height t' < height (lam T t') :=
--          -- by simp [height]
--             -- apply Nat.succ_le_succ
--             -- apply Nat.le_add_left
--             -- auto with 17
--   lam T (inst k.succ (bump 0 e) t')
-- -- termination_by' inst n k e t => Sigma.mk n t
-- termination_by inst t => height t
-- -- decreasing_by simp [InvImage]; try auto

open POrdering DecidableTotalOrder in
def inst' {n} (k : Fin n) (e : Term' m) (hn : n = m.succ) :
  Term' n → Term' m
| bvar i =>
  -- have ⟨a, h⟩ : { a // compare i.val k.val = a } :=
    -- ⟨ _,  rfl ⟩
  match pcompare i.val k.val with
  | isEQ h => e
  | isLT h =>
    have h₀ : i.val < k.val := by
      simp at h; assumption
    have h₁ : k.val ≤ m := Nat.le_of_succ_le_succ <| hn ▸ k.isLt
    bvar ⟨i.val, Nat.lt_of_lt_of_le h₀ h₁⟩
  | isGT h =>
    have : 1 ≤ i.val := by
      simp at h
      trans k.val.succ <;> auto
    have : i.val - 1 < m := Nat.sub_lt_of_lt_add this <| hn ▸ i.isLt
    bvar ⟨i.val - 1,  this⟩
| fvar v => fvar v
| plus t₀ t₁ =>
       -- have : height t₀ < height (plus t₀ t₁) :=
       --   by simp [height];
       --      apply Nat.succ_le_succ
       --      apply Nat.le_add_right
       --   -- by simp [height]; auto
       -- have : height t₁ < height (plus t₀ t₁) :=
       --   by simp [height];
       --      apply Nat.succ_le_succ
       --      apply Nat.le_add_left
       --      -- apply Nat.le_add_of_le_r
       --   --    -- apply Nat.le_add_right
       --   -- by simp [height]; auto
       plus (inst' k e hn t₀) (inst' k e hn t₁)
| Term'.ite c t₀ t₁ =>
       -- have : height c  < height (ite c t₀ t₁) :=
       --   by simp [height];
       --      apply Nat.succ_le_succ
       --      apply Nat.le_add_of_le_l
       --   --    -- apply Nat.le_add_right
       --      apply Nat.le_add_right
       -- have : height t₀ < height (ite c t₀ t₁) :=
       --   by simp [height];
       --      apply Nat.succ_le_succ
       --      apply Nat.le_add_of_le_l
       --   --    -- apply Nat.le_add_right
       --      apply Nat.le_add_left
       --   --    -- auto with 10
       -- have : height t₁ < height (ite c t₀ t₁) :=
       --   by simp [height];
       --      apply Nat.succ_le_succ
       --      -- apply Nat.le_add_of_le_l
       --      apply Nat.le_add_left
       ite (inst' k e hn c) (inst' k e hn t₀) (inst' k e hn t₁)
| app t₀ t₁ =>
       -- have : height t₀ < height (app t₀ t₁) :=
       --   by simp [height]
       --      apply Nat.succ_le_succ
       --      apply Nat.le_add_right
       --   -- by simp [height]; auto
       -- have : height t₁ < height (app t₀ t₁) :=
       --   by simp [height]
       --      apply Nat.succ_le_succ
       --      apply Nat.le_add_left
       --   --    -- auto with 17
       app (inst' k e hn t₀) (inst' k e hn t₁)
| lam T t' =>
  -- have : height t' < height (lam T t') :=
         -- by simp [height]
            -- apply Nat.succ_le_succ
            -- apply Nat.le_add_left
            -- auto with 17
  lam T (inst' k.succ (bump 0 e) (congrArg _ hn) t')
-- termination_by' inst n k e t => Sigma.mk n t
-- termination_by inst t => height t
-- decreasing_by simp [InvImage]; try auto

def inst {n} (k : Fin (succ n)) (e : Term' n) : Term' (succ n) → Term' n :=
inst' k e rfl

def abstr {n} (v : Name) (k : Fin (succ n)) : Term' n → Term' (succ n)
| bvar i =>
  if k.val ≤ i.val then bvar i.succ
  else bvar i.widen
| fvar v' =>
  if v = v' then bvar k
  else fvar v'
| plus t₀ t₁ => plus (abstr v k t₀) (abstr v k t₁)
| app t₀ t₁ => app (abstr v k t₀) (abstr v k t₁)
| ite c t₀ t₁ => ite (abstr v k c) (abstr v k t₀) (abstr v k t₁)
| lam T t => lam T (abstr v k.succ t)

@[auto]
inductive Occurs : {n : Nat} → Name → Term' n → Prop
| fvar : Occurs (n := n) v (fvar v)
| plus₀ {t₀ t₁ : Term' n} : Occurs v t₀ → Occurs v (plus t₀ t₁)
| plus₁ {t₀ t₁ : Term' n} : Occurs v t₁ → Occurs v (plus t₀ t₁)
| ite_c {c t₀ t₁ : Term' n} : Occurs v c → Occurs v (ite c t₀ t₁)
| ite₀ {c t₀ t₁ : Term' n} : Occurs v t₀ → Occurs v (ite c t₀ t₁)
| ite₁ {c t₀ t₁ : Term' n} : Occurs v t₁ → Occurs v (ite c t₀ t₁)
| app₀ {t₀ t₁ : Term' n} : Occurs v t₀ → Occurs v (app t₀ t₁)
| app₁ {t₀ t₁ : Term' n} : Occurs v t₁ → Occurs v (app t₀ t₁)
| lam {T} {t : Term' (succ n)} : Occurs v t → Occurs v (lam T t)

open DecidableTotalOrder (pcompare)

theorem abstr_inst' (v : Name) (k : Fin (succ n)) (k' : Fin m)
        (t : Term' m) (hm : m = succ n) (hk : k.val = k'.val)
        (hv : ¬ Occurs v t):
  abstr v k (inst' k' (fvar v) hm t) = (hm ▸ t) := by
induction t generalizing k n
<;> subst hm
<;> simp [inst', abstr, bump]
next a =>
  -- split
  cases pcompare a.val k'.val
  <;> simp [abstr]
  next h₀ =>
    have h₁ : ¬ k.val ≤ a.val := Nat.not_le_of_gt <| hk ▸ h₀
    simp [if_neg h₁, Fin.widen]
  next h₀ =>
    apply Fin.val_inj
    rw [h₀, hk]
  next h₀ =>
    have h₂ : 0 < a.val := Nat.lt_of_le_of_lt (Nat.zero_le _) h₀
    have h₁ : k.val ≤ a.val - 1 := by
      show _ ≤ a.val.pred
      apply Nat.le_of_succ_le_succ
      rw [Nat.succ_pred h₂, hk]; assumption
    rw [if_pos h₁]; apply congrArg
    apply Fin.val_inj; simp
    apply Nat.le_antisymm
    next =>
      rw [Nat.succ_le_iff]; refl
      apply Nat.lt_of_le_of_lt _ h₀
      auto
    next =>
      rw [Preorder.indirect_le_r]; intro z
      intro h; have h' := h
      have h₃ : 0 < z :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) h'
      rw [Nat.succ_le_iff h₃] at h
      have h : succ a.val.pred ≤ _ := Nat.succ_le_succ h
      simp [Nat.succ_pred,h₂,h₃] at h; assumption
next =>
  split
  next h => subst h; auto [Occurs.fvar]
  next => rfl
next ih₀ ih₁ =>
  rw [ih₀, ih₁] <;> auto
next ih₀ ih₁ ih₂ =>
  rw [ih₀, ih₁, ih₂] <;> auto
next ih₀ ih₁ =>
  rw [ih₀, ih₁] <;> auto
next ih₀ =>
  rw [ih₀]
  . simp; assumption
  . auto

theorem abstr_inst (v : Name) (k : Fin (succ n)) (t : Term' (succ n))
        (hv : ¬ Occurs v t) :
  abstr v k (inst k (fvar v) t) = t := by
simp [inst]; rw [abstr_inst'] <;> auto

-- theorem abstr_inst₀ (v : Name) (k : Fin (succ n)) (t : Term' (succ n)) :
--   abstr v k (inst k e t) = subst v _ t := sorry

theorem inst_abstr (v v' : Name) (k : Fin (succ n)) (t : Term' n) :
        -- (hv : ¬ Occurs v t) :
  inst k e (abstr v k t) = subst v e t := by
admit
-- #check Lean.Name.

def fresh' (n : Nat) : Term' k → Nat
| fvar v =>
  match v with
  | Name.num p n' _ => max n (n' + 1)
  | _ => n
| bvar _ => n
| plus t₀ t₁ =>
  let n := fresh' n t₀
  let n := fresh' n t₁
  n
| ite c t₀ t₁ =>
  let n := fresh' n c
  let n := fresh' n t₀
  let n := fresh' n t₁
  n
| app t₀ t₁ =>
  let n := fresh' n t₀
  let n := fresh' n t₁
  n
| lam T t => fresh' n t

def fresh (t : Term' n) : Name :=
Name.mkNum `x (fresh' 0 t)

theorem le_fresh' (t : Term' k)
  (h : m ≤ n) :
  m ≤ fresh' n t := by
induction t generalizing n
<;> simp [fresh', *]
next =>
  split
  -- next =>
  next => auto [Nat.le_max_l]
  next =>
    auto
next ihc ih₀ ih₁ => auto
  -- -- next => auto
  -- apply ih₁
  -- apply ih₀
  -- apply ihc


theorem not_Occurs_fresh (t : Term' n) :
  ¬ Occurs (fresh t) t := by
suffices ∀ k n : Nat, Occurs (Name.mkNum `x n) t → n < fresh' k t by
  intro h; specialize this 0 _ h
  apply Nat.lt_irrefl _ this
-- suffices ∀ k n : Nat, k ≤ n → Occurs ("x" ++ toString n) t → n < fresh' k t by
  -- intro h; specialize this 0 _ (Nat.zero_le _) h
  -- apply Nat.lt_irrefl _ this

intros m k
-- intros m k h₀
generalize hv : (`x).mkNum k = v; intros h
-- have h' := h
induction h generalizing m
<;> simp [fresh']
<;> try auto [le_fresh']
next v' =>
  simp [← hv, Name.mkNum]
  auto

end Term'

def Term := Term' 0

namespace Term

export Term' (subst fvar plus ite app)
open Term'

-- opaque
def lam (x : Name) (T : Typ) (t : Term) : Term :=
Term'.lam T (abstr x 0 t)

open Term in
inductive View : Term → Type
| fvar {x} :      View (fvar x)
| plus {t₀ t₁} :  View t₀ → View t₁ → View (plus t₀ t₁)
| ite {c t₀ t₁} : View c  → View t₀ → View t₁ → View (Term.ite c t₀ t₁)
| app {t₀ t₁} :   View t₀ → View t₁ → View (app t₀ t₁)
| lam {x T t} :   View t  → View (lam x T t)

-- def insts : (vs : List Name) → Term' vs.length → Term
-- | [], t => t
-- | v :: vs, t => insts vs <| inst 0 (fvar v) t
-- #check Fin.cast
def insts' (k : Nat) (vs : List (Term' k)) (h : n = vs.length + k) :
  Term' n → Term' k
| bvar i =>
  if h' : i.val < k
  then bvar <| i.cast h |>.cutl' h'
  else vs.get <| i.cast h |>.cutr' h'
  -- match Fin.split (i.cast h) with
  -- | Sum.inl i => vs.get i
  -- | Sum.inr i => bvar i
| fvar x => fvar x
| app t₀ t₁  => app (insts' k vs h t₀) (insts' k vs h t₁)
| plus t₀ t₁ => plus (insts' k vs h t₀) (insts' k vs h t₁)
| Term'.ite c t₀ t₁ =>
  ite (insts' k vs h c) (insts' k vs h t₀) (insts' k vs h t₁)
| Term'.lam T t =>
Term'.lam T <|
  insts' k.succ (bump 0 <$> vs)
    (by simp [succ_add,h]) t

open DecidableTotalOrder

-- -- (by simp [h₀, Nat.succ_add])
@[simp]
theorem insts_cons
        (vs : List (Term' k))
        (t : Term' n)
        (h₀ : n = List.length (t' :: vs) + k)
        (h₁ : _ = _) :
        -- (h₁ : n = List.length vs) :
  insts' _ (t' :: vs) h₀ t =
  inst' Fin.last t' rfl (insts' k.succ (bump 0 <$> vs) h₁ t) := by
induction t
 <;> simp [insts', Fin.split]
next a =>
  split; split
  next h₀ h₁ =>
    simp [inst']; split
    next h₇ h₈ =>
      clear h₈; simp [inst'] at *
      rw [h₇] at h₀; cases Nat.lt_irrefl _ h₀
    next =>
      apply congrArg; apply Fin.val_inj
      simp
    next =>
      skip
      apply congrArg; apply Fin.val_inj
      simp

  -- next h => rw [h]
  -- inst k _ (insts' (bump 0 <$> vs) _ t) := by
--   -- insts' vs h₁ (inst' i t' (by simp [h₀, h₁]) t) := by
-- induction t
-- <;> simp [insts', inst']
-- next j =>
--   cases pcompare j.val i.val <;> simp [insts']
--   next h₃ =>
--     rw [h₂] at h₃; cases Nat.not_lt_zero _ h₃
--   next h₃ =>
--     rw [h₂] at h₃; cases j; subst h₃; rfl
skip

-- #exit

def insts (vs : List (Term' m)) (t : Term' (vs.length + m)) : Term' m :=
insts' _ vs rfl t

-- #exit
-- #check Nat.add
def view' {vs} (hn : n = vs.length)
  (hf : ∀ i, View (vs.get i)) :
  (t : Term' n) → View (insts' 0 vs hn t)
| bvar x =>
  let x' : Fin (n + 0) := x
  -- have h₀ : Fin.split (x.cast _ : Fin (vs.length + 0)) = Sum.inl (hn ▸ x : Fin vs.length) := by
    -- simp [Fin.split]; rw [dif_pos]
  have h₀ : x.val < List.length vs := hn ▸ x.isLt
  suffices View (vs.get <| x.cast hn) by
    simp [insts', dif_pos h₀]
    exact this
  hf _
| fvar x => View.fvar
| plus t₀ t₁ => View.plus (view' _ hf t₀) (view' _ hf t₁)
| app t₀ t₁ => View.app (view' _ hf t₀) (view' _ hf t₁)
| ite c t₀ t₁ => View.ite (view' _ hf c) (view' _ hf t₀) (view' _ hf t₁)
| Term'.lam T t =>
  let x := fresh t
  show View (Term'.lam _ _) from
  -- have h :=
  by rw [← abstr_inst x 0 (insts' (succ 0) (bump 0 <$> vs) _ t)]
     apply View.lam
  -- by simp [insts']


def view : (t : Term) → View t
| fvar x => View.fvar
| plus t₀ t₁ => View.plus (view t₀) (view t₁)
| app t₀ t₁ => View.app (view t₀) (view t₁)
| ite c t₀ t₁ => View.ite (view c) (view t₀) (view t₁)
| Term'.lam T t =>
  let x := fresh t
  have : t = abstr x 0 (inst 0 (fvar x) t) :=
    abstr_inst _ _ _ (Term'.not_Occurs_fresh _) |>.symm
  -- View.lam <| view <| inst 0 (fvar x) t
  _

end Term
