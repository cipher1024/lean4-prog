
import Lib.Data.Nat
import Lib.Data.Ordering
import Lib.Data.List.Basic
import Lib.Meta.DeclGraph
import Lib.Meta.Dump
import Lib.Meta.Opaque
import Lib.Meta.TransportFacts
import Lib.Order.Basic

macro_rules
| `(tactic| decreasing_tactic) =>
 `(tactic|
   (simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel]
    repeat (first | apply Prod.Lex.right | apply Prod.Lex.left)
    repeat (first | apply PSigma.Lex.right | apply PSigma.Lex.left)
    simp [Nat.add_comm (n := 1), Nat.succ_add, Nat.mul_succ]
    try apply Nat.lt_succ_of_le
    repeat apply Nat.le_step
    first
    | repeat first | apply Nat.le_add_left | apply Nat.le_add_of_le_l
    | assumption
    all_goals apply Nat.le_refl ))
-- #check @cast_eq
-- theorem cast_eq {α} (h : α = α) (x) :
  -- cast h x = x := rfl

theorem cast_cast {α β} (h : α = β) (h' : β = α) (x) :
  cast h (cast h' x) = x := by
cases h; cases h'; rfl

theorem cast_app {α α' β β'} (h : α' = α) (h' : β = β') (f : α → β) x :
  cast h' (f (cast h x)) = (cast (by rw [h,h']) f : α' → β') x :=
by substAll; simp [cast_eq]

structure Equiv (α β : Sort u) where
  to : α → β
  inv : β → α
  to_inv x : to (inv x) = x
  inv_to x : inv (to x) = x

attribute [simp] Equiv.to_inv Equiv.inv_to

def Equiv.R (h : Equiv α β) x y :=
h.to x = y ∧ x = h.inv y

def Equiv.refl : Equiv α α where
  to := id
  inv := id
  to_inv x := rfl
  inv_to x := rfl

def Equiv.symm (h₀ : Equiv α β) : Equiv β α where
  to := h₀.inv
  inv := h₀.to
  inv_to := h₀.to_inv
  to_inv := h₀.inv_to

def Equiv.trans (h₀ : Equiv α β) (h₁ : Equiv β γ) : Equiv α γ where
  to x  := h₁.to (h₀.to x)
  inv x := h₀.inv (h₁.inv x)
  to_inv x := by simp
  inv_to x := by simp

def Eq.toEquiv {α β : Type u} (h : α = β) : Equiv α β where
  to  := cast h
  inv := cast h.symm
  to_inv := cast_cast _ _
  inv_to := cast_cast _ _

-- def Eq.toEquiv {α β : Type u} (h : Equiv α β) : α = β := _

-- class EquivRel.{v,u} (T : Sort u) where
--   R : T → T → Sort v
--   refl x : R x x
--   trans x y z : R x y → R y z → R x z
--   -- to_eq x y : R x y → x = y

class IsSetoid (α : Sort u) [HasEquiv α] where
  refl (x : α) : x ≈ x
  symm (x y : α) : x ≈ y → y ≈ x
  trans (x y z : α) : x ≈ y → y ≈ z → x ≈ z

instance : HasEquiv (Sort u) where
  Equiv α β := Equiv α β

instance : IsSetoid (Sort u) where
  refl := @Equiv.refl
  symm := @Equiv.symm
  trans := @Equiv.trans
-- #check Reflexive

instance [HasEquiv.{v,u} α] [HasEquiv.{v',u'} β] : HasEquiv (α → β) where
  Equiv f g := ∀ x y, HasEquiv.Equiv x y → HasEquiv.Equiv (f x) (g y)

-- structure LockedType {T : Sort u} (T' : Sort u) [HasEquiv.{u,v} T] (x : T) where

namespace Subtype

theorem val_inj {p : α → Prop} {x y : Subtype p}
        (h : x.val = y.val) :
  x = y := by cases x; cases y; cases h; rfl

end Subtype

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

inductive NTerm' : Type
| fvar : Name → NTerm'
| plus (t₀ t₁ : NTerm') : NTerm'
| ite (c t₀ t₁ : NTerm') : NTerm'
| app (t₀ t₁ : NTerm') : NTerm'
| lam : Name → Typ → NTerm' → NTerm'

namespace NTerm'

-- does not avoid capture. Ugh
def subst (v : Name) (e : NTerm') : NTerm' → NTerm'
| fvar n =>
  if v == n then e else fvar n
| plus t₀ t₁ =>
  plus (subst v e t₀) (subst v e t₁)
| app t₀ t₁ =>
  app (subst v e t₀) (subst v e t₁)
| ite c t₀ t₁ =>
  ite (subst v e c) (subst v e t₀) (subst v e t₁)
| lam x T t =>
  if x == v then
    lam x T t
  else lam x T (subst v e t)

inductive AlphaEqv : NTerm' → NTerm' → Prop
| fvar : AlphaEqv (fvar v) (fvar v')
| plus :
  AlphaEqv ta₀ tb₀ → AlphaEqv ta₁ tb₁ →
  AlphaEqv (plus ta₀ ta₁) (plus tb₀ tb₁)
| app :
  AlphaEqv ta₀ tb₀ → AlphaEqv ta₁ tb₁ →
  AlphaEqv (app ta₀ ta₁) (app tb₀ tb₁)
| ite :
  AlphaEqv ca cb → AlphaEqv ta₀ tb₀ → AlphaEqv ta₁ tb₁ →
  AlphaEqv (ite ca ta₀ ta₁) (ite cb tb₀ tb₁)
| lam :
  (∀ z, AlphaEqv (subst x (fvar z) ta) (subst y (fvar z) tb)) →
  AlphaEqv (lam x T ta) (lam y T tb)

end NTerm'

inductive Term' : Type
| bvar : Nat → Term'
| fvar : Name → Term'
| plus (t₀ t₁ : Term') : Term'
| ite (c t₀ t₁ : Term') : Term'
| app (t₀ t₁ : Term') : Term'
| lam : Typ → Term' → Term'

namespace Term'

@[auto]
inductive Bounded : Term' → Nat → Prop
| bvar {v b} : v < b → Bounded (bvar v) b
| fvar : Bounded (fvar n) b
| plus : Bounded t₀ b → Bounded t₁ b → Bounded (plus t₀ t₁) b
| ite : Bounded c b → Bounded t₀ b → Bounded t₁ b → Bounded (ite c t₀ t₁) b
| app : Bounded t₀ b → Bounded t₁ b → Bounded (app t₀ t₁) b
| lam : Bounded t (succ b) → Bounded (lam T t) b

def bump (k : Nat) : Term' → Term'
| bvar i =>
  if k ≤ i then bvar i.succ else bvar i
| fvar v => fvar v
| plus t₀ t₁ => plus (bump k t₀) (bump k t₁)
| Term'.ite c t₀ t₁ => ite (bump k c) (bump k t₀) (bump k t₁)
| app t₀ t₁ => app (bump k t₀) (bump k t₁)
| lam T t => lam T (bump k.succ t)

def subst (v : Name) (e : Term') : Term' → Term'
| bvar i => bvar i
| fvar v' =>
  if v = v' then e else fvar v'
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

@[simp]
def height : Term' → Nat
| bvar _ => 0
| fvar _ => 0
| plus t₀ t₁ => 1 + height t₀ + height t₁
-- | plus t₀ t₁ => 1 + height t₀ + height t₁
| app t₀ t₁ => 1 + height t₀ + height t₁
-- | app t₀ t₁ => height t₀ + height t₁ + 1
| Term'.ite c t₀ t₁ => 1 + height c + height t₀ + height t₁
-- | Term'.ite c t₀ t₁ => height c + height t₀ + height t₁ + 1
| lam T t => 1 + height t
-- | lam T t => height t + 1

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
def inst' (k : Nat) (e : Term')  :
  Term' → Term'
| bvar i =>
  -- have ⟨a, h⟩ : { a // compare i.val k.val = a } :=
    -- ⟨ _,  rfl ⟩
  match pcompare i k with
  | isEQ h => e
  | isLT h =>
    -- have h₀ : i < k := by
    --   simp at h; assumption
    -- have h₁ : k ≤ m := Nat.le_of_succ_le_succ <| hn ▸ k.isLt
    bvar i
  | isGT h =>
    -- have : 1 ≤ i.val := by
    --   simp at h
    --   trans k.val.succ <;> auto
    -- have : i.val - 1 < m := Nat.sub_lt_of_lt_add this <| hn ▸ i.isLt
    bvar <| i - 1
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
       plus (inst' k e t₀) (inst' k e t₁)
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
       ite (inst' k e c) (inst' k e t₀) (inst' k e t₁)
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
       app (inst' k e t₀) (inst' k e t₁)
| lam T t' =>
  -- have : height t' < height (lam T t') :=
         -- by simp [height]
            -- apply Nat.succ_le_succ
            -- apply Nat.le_add_left
            -- auto with 17
  lam T (inst' k.succ (bump 0 e) t')
-- termination_by' inst n k e t => Sigma.mk n t
-- termination_by inst t => height t
-- decreasing_by simp [InvImage]; try auto

-- def inst {n} (k : Fin (succ n)) (e : Term' n) : Term' (succ n) → Term' n :=
-- inst' k e rfl

def abstr (v : Name) (k : Nat) : Term' → Term'
| bvar i =>
  if k ≤ i then bvar i.succ
  else bvar i
| fvar v' =>
  if v = v' then bvar k
  else fvar v'
| plus t₀ t₁ => plus (abstr v k t₀) (abstr v k t₁)
| app t₀ t₁ => app (abstr v k t₀) (abstr v k t₁)
| ite c t₀ t₁ => ite (abstr v k c) (abstr v k t₀) (abstr v k t₁)
| lam T t => lam T (abstr v k.succ t)

@[auto]
inductive Occurs : Name → Term' → Prop
| fvar : Occurs v (fvar v)
| plus₀ {t₀ t₁ : Term'} : Occurs v t₀ → Occurs v (plus t₀ t₁)
| plus₁ {t₀ t₁ : Term'} : Occurs v t₁ → Occurs v (plus t₀ t₁)
| ite_c {c t₀ t₁ : Term'} : Occurs v c → Occurs v (ite c t₀ t₁)
| ite₀ {c t₀ t₁ : Term'} : Occurs v t₀ → Occurs v (ite c t₀ t₁)
| ite₁ {c t₀ t₁ : Term'} : Occurs v t₁ → Occurs v (ite c t₀ t₁)
| app₀ {t₀ t₁ : Term'} : Occurs v t₀ → Occurs v (app t₀ t₁)
| app₁ {t₀ t₁ : Term'} : Occurs v t₁ → Occurs v (app t₀ t₁)
| lam {T} {t : Term'} : Occurs v t → Occurs v (lam T t)

open DecidableTotalOrder (pcompare)

theorem abstr_inst' (v : Name) (k : Nat) (t : Term')
        (hv : ¬ Occurs v t):
  abstr v k (inst' k (fvar v) t) = t := by
induction t generalizing k
-- <;> subst hm
<;> simp [inst', abstr, bump]
<;> try solve | simp [*]
next a =>
  -- split
  cases pcompare a k
  <;> simp [abstr, inst']
  next h₀ =>
    have h₁ : ¬ k ≤ a := Nat.not_le_of_gt h₀
    simp [if_neg h₁]
  next h₀ => exact h₀.symm
  next h₀ =>
    have h₂ : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le _) h₀
    have h₆ : succ (pred a) = a :=
      by rw [Nat.succ_pred h₂]
    have h₅ : succ (a - 1) = a := h₆
    have h₁ : k ≤ a - 1 := by
      apply Nat.le_of_succ_le_succ
      rw [h₅]; assumption
    rw [if_pos h₁]; apply congrArg
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
      have h : succ a.pred ≤ _ := Nat.succ_le_succ h
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
  rw [ih₀]; auto

theorem abstr_inst (v : Name) (k : Nat) (t : Term')
        (hv : ¬ Occurs v t) :
  abstr v k (inst' k (fvar v) t) = t := by
simp [inst']; rw [abstr_inst'] <;> auto

-- theorem abstr_inst₀ (v : Name) (k : Fin (succ n)) (t : Term' (succ n)) :
--   abstr v k (inst k e t) = subst v _ t := sorry

theorem inst_abstr (v v' : Name) (k : Nat) (t : Term') :
        -- (hv : ¬ Occurs v t) :
  inst' k e (abstr v k t) = subst v e t := by
admit

-- #check Lean.Name.

def fresh' (n : Nat) : Term' → Nat
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

def fresh (t : Term') : Name :=
Name.mkNum `x (fresh' 0 t)

theorem le_fresh' (t : Term')
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


theorem not_Occurs_fresh (t : Term') :
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

-- namespace Bounded

-- @[auto]
-- theorem Bounded_plus
--         (h₀ : Bounded t₀ n)
--         (h₁ : Bounded t₁ n) :
--   Bounded (plus t₀ t₁) n := by

@[auto]
theorem Bounded_bump
        (h : Bounded t n) :
  Bounded (bump k t) (succ n) := by
induction h generalizing k <;> simp [bump]
<;> split* <;> auto

@[auto]
theorem Bounded_inst
        (h₀ : Bounded x n)
        (h₁ : Bounded t (succ n))
        (h₂ : k ≤ n) :
  Bounded (inst' k x t) n := by
induction t generalizing x n k
<;> simp [inst']
<;> cases h₁
<;> solve
    | split*
      <;> auto
split <;>
  repeat
    first
    | assumption
    | constructor
case bvar.bvar.h_2.a h₀ h₁ =>
  apply Nat.lt_of_lt_of_le h₀ h₂
case bvar.bvar.h_3.a a _ h₀ h₁ h₂ =>
  apply Nat.le_of_succ_le_succ
  have → : succ (a - 1) = a := by
    show succ (pred a) = a
    rw [Nat.succ_pred]
    apply Nat.lt_of_le_of_lt (m := k) <;> auto
  assumption

@[auto]
theorem Bounded_abstr
        (h : Bounded t n)
        (h' : k ≤ n) :
  Bounded (abstr x k t) (succ n) := by
induction t generalizing n k
<;> simp [abstr]
<;> cases h
<;> solve
    | split*
      <;> auto

end Term'
  -- transport x := cast (by rw [@EqvTypes.rfl α α', @EqvTypes.rfl β β']) x
  -- transport_eq x := by
  --   have h₀ := @EqvTypes.rfl α α' _
  --   have h₁ := @EqvTypes.rfl β β' _
  --   substAll
  --   constructor

namespace Term.Impl
open Transport

-- def Term := { t // Term'.Bounded t 0 }
opaque def Term := { t // Term'.Bounded t 0 }

-- #pred HEq

@[auto]
instance : EqvTypes Term._def Term where
  rfl := Term._unlock.symm
  -- transport x := cast Term._unlock.symm x
  -- transport_eq x := by
  --   have h := Term._unlock


-- export Term' (subst fvar plus ite app)
open Term'

-- -- #print Eq
-- -- @[elab declaration]
-- -- def elabDeclaration : Lean.Elab.Command.CommandElab := fun stx => do
--   -- throwError "my elab"
-- elab_rules : command
-- | `($d:«def») => _

-- elab_rules : command
-- | `($d:declaration) => println!"my elab"
-- elab (d:declaration) : command =>
--   println!"my elab"

-- opaque
-- @[transport foo]
def fvar (x : Name) : Term._def :=
⟨ Term'.fvar x, by auto ⟩

#exit

constant fvar_locked : LockedType (Name → Term) (fvar) :=
mkLockedType _ _

def fvar' : Name → Term := fvar_locked.val

theorem fvar'._unlock : fvar' ~= fvar := fvar_locked.val_eqv

@[auto]
instance : EqvTerm fvar fvar' where
  rfl := fvar'._unlock.symm

-- opaque
def plus : Term._def → Term._def → Term._def
| ⟨t₀,h₀⟩, ⟨t₁,h₁⟩ =>
⟨ Term'.plus t₀ t₁, by auto ⟩

constant plus_locked : LockedType (Term → Term → Term) plus :=
mkLockedType _ _

def plus' : Term → Term → Term := plus_locked.val

theorem plus'._unlock : plus' ~= plus := plus_locked.val_eqv

instance : EqvTerm plus plus' where
  rfl := plus'._unlock.symm

-- opaque
def app : Term._def → Term._def → Term._def
| ⟨t₀,h₀⟩, ⟨t₁,h₁⟩ =>
⟨ Term'.app t₀ t₁, by auto ⟩

constant app_locked : LockedType (Term → Term → Term) app :=
mkLockedType _ _

def app' : Term → Term → Term := app_locked.val

theorem app'._unlock : app' ~= app := app_locked.val_eqv

instance : EqvTerm app app' where
  rfl := app'._unlock.symm

-- opaque
def ite : Term._def → Term._def → Term._def → Term._def
| ⟨c,hc⟩, ⟨t₀,h₀⟩, ⟨t₁,h₁⟩ =>
⟨ Term'.ite c t₀ t₁, by auto ⟩

constant ite_locked : LockedType (Term → Term → Term → Term) ite :=
mkLockedType _ _

def ite' : Term → Term → Term → Term := ite_locked.val

theorem ite'._unlock : ite' ~= ite := ite_locked.val_eqv

instance : EqvTerm ite ite' where
  rfl := ite'._unlock.symm

-- opaque
def lam (x : Name) (T : Typ) : Term._def → Term._def
| ⟨t, ht⟩ =>
⟨Term'.lam T (abstr x 0 t), by auto ⟩

constant lam_locked : LockedType (Name → Typ → Term → Term) lam :=
mkLockedType _ _

def lam' : Name → Typ → Term → Term := lam_locked.val

theorem lam'._unlock : lam' ~= lam := lam_locked.val_eqv

-- #exit

def inst (x : Name) (t : Term') (h : Bounded t 1) : Term._def :=
⟨ Term'.inst' 0 (Term'.fvar x) t, by auto ⟩

@[simp]
theorem val_lam : (lam x T t).val = Term'.lam T (abstr x 0 t.val) := rfl

@[simp]
theorem val_inst : (inst x t h).val = inst' 0 (Term'.fvar x) t := rfl

open Term in
inductive View : Term._def → Type
| fvar {x} :      View (fvar x)
| plus {t₀ t₁} :  View t₀ → View t₁ → View (plus t₀ t₁)
| ite {c t₀ t₁} : View c  → View t₀ → View t₁ → View (ite c t₀ t₁)
| app {t₀ t₁} :   View t₀ → View t₁ → View (app t₀ t₁)
| lam {x T t} :   View t  → View (lam x T t)

-- -- def insts : (vs : List Name) → Term' vs.length → Term
-- -- | [], t => t
-- -- | v :: vs, t => insts vs <| inst 0 (fvar v) t
-- -- #check Fin.cast
-- def insts' (k : Nat) (vs : List (Term' k)) (h : n = vs.length + k) :
--   Term' n → Term' k
-- | bvar i =>
--   if h' : i.val < k
--   then bvar <| i.cast h |>.cutl' h'
--   else vs.get <| i.cast h |>.cutr' h'
--   -- match Fin.split (i.cast h) with
--   -- | Sum.inl i => vs.get i
--   -- | Sum.inr i => bvar i
-- | fvar x => fvar x
-- | app t₀ t₁  => app (insts' k vs h t₀) (insts' k vs h t₁)
-- | plus t₀ t₁ => plus (insts' k vs h t₀) (insts' k vs h t₁)
-- | Term'.ite c t₀ t₁ =>
--   ite (insts' k vs h c) (insts' k vs h t₀) (insts' k vs h t₁)
-- | Term'.lam T t =>
-- Term'.lam T <|
--   insts' k.succ (bump 0 <$> vs)
--     (by simp [succ_add,h]) t

open DecidableTotalOrder

-- -- -- (by simp [h₀, Nat.succ_add])
-- @[simp]
-- theorem insts_cons
--         (vs : List (Term' k))
--         (t : Term' n)
--         (h₀ : n = List.length (t' :: vs) + k)
--         (h₁ : _ = _) :
--         -- (h₁ : n = List.length vs) :
--   insts' _ (t' :: vs) h₀ t =
--   inst' Fin.last t' rfl (insts' k.succ (bump 0 <$> vs) h₁ t) := by
-- induction t
--  <;> simp [insts', Fin.split]
-- next a =>
--   split; split
--   next h₀ h₁ =>
--     simp [inst']; split
--     next h₇ h₈ =>
--       clear h₈; simp [inst'] at *
--       rw [h₇] at h₀; cases Nat.lt_irrefl _ h₀
--     next =>
--       apply congrArg; apply Fin.val_inj
--       simp
--     next =>
--       skip
--       apply congrArg; apply Fin.val_inj
--       simp

--   -- next h => rw [h]
--   -- inst k _ (insts' (bump 0 <$> vs) _ t) := by
-- --   -- insts' vs h₁ (inst' i t' (by simp [h₀, h₁]) t) := by
-- -- induction t
-- -- <;> simp [insts', inst']
-- -- next j =>
-- --   cases pcompare j.val i.val <;> simp [insts']
-- --   next h₃ =>
-- --     rw [h₂] at h₃; cases Nat.not_lt_zero _ h₃
-- --   next h₃ =>
-- --     rw [h₂] at h₃; cases j; subst h₃; rfl
-- skip

-- -- #exit

-- def insts (vs : List (Term' m)) (t : Term' (vs.length + m)) : Term' m :=
-- insts' _ vs rfl t

-- -- @[simp]
-- theorem dec_1 p q : p < 1 + p + q := sorry
-- theorem dec_2 p q : q < 1 + p + q := sorry

@[simp]
theorem height_inst' k x t :
  height (inst' k (Term'.fvar x) t) = height t := by
induction t generalizing k
<;> simp [inst', *, bump]
split <;> rfl

-- @[simp]
-- theorem dec_3 p q : p < q + p ↔ 0 < q := sorry
attribute [scoped simp] inst' in
-- #exit
-- #check Nat.add
def view' :
  (t : Term') → (h : Bounded t 0) → View ⟨t,h⟩
-- | bvar x, Bounded =>
  -- let x' : Fin (n + 0) := x
  -- have h₀ : Fin.split (x.cast _ : Fin (vs.length + 0)) = Sum.inl (hn ▸ x : Fin vs.length) := by
    -- simp [Fin.split]; rw [dif_pos]
  -- have h₀ : x.val < List.length vs := hn ▸ x.isLt
  -- suffices View (vs.get <| x.cast hn) by
  --   simp [insts', dif_pos h₀]
  --   exact this
  -- hf _

| Term'.bvar x, h => False.elim <| by
  cases h with | bvar h => cases (Nat.not_lt_zero _ h)
| Term'.fvar x, h => View.fvar
| Term'.plus t₀ t₁, h =>
  have : height t₀ < 1 + height t₀ + height t₁ := sorry
  have : height t₁ < 1 + height t₀ + height t₁ := sorry
  View.plus (view' t₀ (by cases h; auto)) (view' t₁ (by cases h; auto))
| Term'.app t₀ t₁, h =>
  have : height t₀ < 1 + height t₀ + height t₁ := sorry
  have : height t₁ < 1 + height t₀ + height t₁ := sorry
  View.app (view' t₀ (by cases h; auto)) (view' t₁ (by cases h; auto))
| Term'.ite c t₀ t₁, h =>
  have : height c < 1 + height c + height t₀ + height t₁ := sorry
  have : height t₀ < 1 + height c + height t₀ + height t₁ := sorry
  have : height t₁ < 1 + height c + height t₀ + height t₁ := sorry
  View.ite (view' c (by cases h; auto))
    (view' t₀ (by cases h; auto))
    (view' t₁ (by cases h; auto))
| Term'.lam T t, h =>
  let x := fresh t
  -- cases h
  have h₂ : Bounded t 1 := sorry
  -- have h' : Bounded (Term'.lam T (abstr x 0 (inst' 0 (Term'.fvar x) t))) 0 := sorry
  have : height t < 1 + height t := sorry
  suffices View (lam x T (inst x t h₂)) by
    -- unfold lam at this
    have h' := not_Occurs_fresh t
    apply cast _ this; apply congrArg
    apply Subtype.val_inj
    simp [abstr_inst', h']
    -- h'; simp only [lam, inst]
    -- simp [abstr_inst]
    -- revert h'
    -- apply not_Occurs_fresh
  View.lam (view' (inst' _ _ t) _)
  -- let x := fresh t
  -- show View (Term'.lam _ _) from
  -- -- have h :=
  -- by rw [← abstr_inst x 0 (insts' (succ 0) (bump 0 <$> vs) _ t)]
  --    apply View.lam
  -- -- by simp [insts']
termination_by view' t _ => height t

def view :
  (t : Term._def) → View t
| ⟨t,ht⟩ => view' t ht

section rec
variable {motive : Term._def → Sort u}
variable (Hvar : (v : Name) → motive (fvar v))
variable (Happ : (t₀ t₁ : Term._def) → motive t₀ → motive t₁ → motive (app t₀ t₁))
variable (Hplus : (t₀ t₁ : Term._def) → motive t₀ → motive t₁ → motive (plus t₀ t₁))
variable (Hite : (c t₀ t₁ : Term._def) →
         motive c → motive t₀ → motive t₁ →
         motive (ite c t₀ t₁))
variable (Hlam : ∀ x T,
         (t : Term._def) →
         motive t →
         motive (lam x T t))

def Hvar' : (v : Name) → motive (fvar v) := sorry

elab "trace" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  print_vars![Lean.asGoal g]

-- macro "haveI " " : " p:term ":=" proof:term : term =>
  -- `
-- #print auto_db
-- #check instEqvTypesForAllForAll
-- set_option pp.explicit true in
-- #check @Hvar'.{u}
-- #check mkLockedType
-- #check @instEqvTypesForAllForAll
-- set_option trace.auto.lemmas true

def new : LockedType
  ({motive : Term → Sort u} → ((v : Name) → motive (fvar' v)))
  (@Hvar'.{u}) :=
-- have : EqvTypes (Term._def → Sort u) (Term → Sort u) :=
--   inferInstance
-- have : ∀ (x : Term._def → Sort u) (y : Term → Sort u),
--      EqvTerm x y → EqvTypes
--        (((v : Name) → x (fvar v)))
--        ((v : Name) → y (fvar' v)) :=
--      λ x y Hxy =>
--        have : ∀ (n : Name) (n' : Name), EqvTerm n n' →
--             EqvTypes (x (fvar n)) (y (fvar' n')) := sorry
--        @instEqvTypesForAllForAll Name Name _ _ _
--          -- (λ n => x (fvar n))
--          -- (λ n => y (fvar' n))
--          this
-- have : EqvTypes
--   ({motive : Term._def → Sort u} → ((v : Name) → motive (fvar v)))
--   ({motive : Term → Sort u} → ((v : Name) → motive (fvar' v))) := by
--   -- @instEqvTypesForAllForAll _ _ _ _ _ this
--   -- eauto
--   eauto_step
--   focus
--     eauto [bar_foo] with 15

    -- eauto_step
    -- admit
    -- eauto_step
  -- apply d
  -- auto_step
  -- auto_step
  -- apply d
  -- eauto_step
  -- eauto_step
  -- eauto_step
  -- -- auto_step
mkLockedType _
  (by
  prove_transport
  )
  _

#exit

def rec' : (t : Term._def) → View t → motive t
| _, View.fvar => Hvar _
| _, View.plus t₀ t₁ => Hplus _ _ (rec' _ t₀) (rec' _ t₁)
| _, View.app t₀ t₁ => Happ _ _ (rec' _ t₀) (rec' _ t₁)
| _, View.ite c t₀ t₁ => Hite _ _ _ (rec' _ c) (rec' _ t₀) (rec' _ t₁)
| _, View.lam t => Hlam _ _ _ (rec' _ t)

def rec (t : Term._def) : motive t :=
rec' Hvar Happ Hplus Hite Hlam t (view t)


-- have v := view t
-- let motive' t (v : View t) := motive t
-- show motive' t v
-- skip
-- refine View.rec _ _ _ _ _ v

-- induction v <;>
-- first
-- | auto
-- | try apply_assumption <;> assumption


end rec

end Term.Impl

opaque def Term := Term.Impl.Term
-- constant Term_def : LockedType Term.Impl.Term :=
-- { val := Term.Impl.Term
--   val_eqv := Equiv.refl }

-- def Term._eqv : Term ≈ Term.Impl.Term :=
-- by rw [Term._unlock]; apply Equiv.refl

-- #exit

namespace Term

opaque def fvar (v : Name) : Term :=
-- suffices Name → Term.Impl.Term
  -- by rw [Term._unlock]; exact this
cast Term._unlock.symm (Term.Impl.fvar v)

opaque def app (t₀ t₁ : Term) : Term :=
-- suffices Term.Impl.Term → Term.Impl.Term → Term.Impl.Term
--   by rw [Term._unlock]; exact this
-- Term.Impl.app
cast Term._unlock.symm
  (Impl.app (cast Term._unlock t₀) (cast Term._unlock t₁))

opaque def ite (c t₀ t₁ : Term) : Term :=
-- suffices Term.Impl.Term → Term.Impl.Term → Term.Impl.Term
--   by rw [Term._unlock]; exact this
-- Term.Impl.app
cast Term._unlock.symm
  (Impl.ite
    (cast Term._unlock c)
    (cast Term._unlock t₀) (cast Term._unlock t₁))

--  : Term → Term → Term → Term :=
-- suffices Term.Impl.Term → Term.Impl.Term → Term.Impl.Term → Term.Impl.Term
--   by rw [Term._unlock]; exact this
-- Term.Impl.ite

opaque def plus (t₀ t₁ : Term) : Term :=
cast Term._unlock.symm
  (Impl.plus (cast Term._unlock t₀) (cast Term._unlock t₁))

-- suffices Term.Impl.Term → Term.Impl.Term → Term.Impl.Term
--   by rw [Term._unlock]; exact this
-- Term.Impl.plus

opaque def lam (n : Name) (T : Typ) (t : Term) : Term :=
cast Term._unlock.symm
  (Impl.lam n T (cast Term._unlock t))

--  : Name → Typ → Term → Term :=
-- suffices Name → Typ → Term.Impl.Term → Term.Impl.Term
--   by rw [Term._unlock]; exact this
-- Term.Impl.lam

inductive Eqv : Term → Impl.Term → Type
| fvar : Eqv (Term.fvar x) (Impl.fvar x)
| plus : Eqv ta₀ tb₀ → Eqv ta₁ tb₁ →
  Eqv (Term.plus ta₀ ta₁) (Impl.plus tb₀ tb₁)
| app : Eqv ta₀ tb₀ → Eqv ta₁ tb₁ →
  Eqv (Term.app ta₀ ta₁) (Impl.plus tb₀ tb₁)
| ite : Eqv ca cb → Eqv ta₀ tb₀ → Eqv ta₁ tb₁ →
  Eqv (Term.ite ca ta₀ ta₁) (Impl.ite cb tb₀ tb₁)
| lam : Eqv ta tb →
  Eqv (Term.lam x T ta) (Impl.lam x T tb)


-- inductive View : Term → Type
-- | fvar {x} :      View (fvar x)
-- | plus {t₀ t₁} :  View t₀ → View t₁ → View (plus t₀ t₁)
-- | ite {c t₀ t₁} : View c  → View t₀ → View t₁ → View (ite c t₀ t₁)
-- | app {t₀ t₁} :   View t₀ → View t₁ → View (app t₀ t₁)
-- | lam {x T t} :   View t  → View (lam x T t)

-- noncomputable def View.equiv.to : {t : Term} → {t' : Impl.Term} → Eqv t t' →
--    (View t) → (Impl.View t')
-- | _, _, Eqv.fvar, View.fvar => Impl.View.fvar
-- | _, _, Eqv.plus h₀ h₁, _ => _
-- | _, _, Eqv.app h₀ h₁, _ => _
-- | _, _, Eqv.ite hc h₀ h₁, _ => _
-- | _, _, Eqv.lam h₁, _ => _

-- def View.equiv {t t'} : Eqv t t' →
--   Equiv (View t) (Impl.View t') := by
-- intro h
-- -- cases t' with | mk t' ht' =>
-- -- have v := Impl.view t'
-- induction h with
-- | fvar =>
--   skip



-- def view t : View t := by
-- obtain ⟨t', ht⟩ : { t' : Impl.Term // t = cast Term._unlock.symm t' }
--   from ⟨_, cast_cast Term._unlock.symm Term._unlock t |>.symm  ⟩
-- have h := Impl.view t'
-- cases h
-- <;> rw [ht]

-- opaque def view :

theorem cast_app' {α α' β β'} (h : α = α') (h' : β = β') (f : α → β) x :
  cast h' (f x) = (cast (by rw [h,h']) f : α' → β') (cast h x) :=
by rw [← cast_app h.symm h', cast_cast]

theorem cast_app'' {α β β'} (h' : β = β') (f : α → β) x :
  cast h' (f x) = (cast (by rw [h']) f : α → β') x :=
cast_app' rfl _ f x

-- #print fvar._def

section rec
variable {motive : Term → Sort u}
variable (Hvar : (v : Name) → motive (fvar v))
variable (Happ : (t₀ t₁ : Term) → motive t₀ → motive t₁ → motive (app t₀ t₁))
variable (Hplus : (t₀ t₁ : Term) → motive t₀ → motive t₁ → motive (plus t₀ t₁))
variable (Hite : (c t₀ t₁ : Term) →
         motive c → motive t₀ → motive t₁ →
         motive (ite c t₀ t₁))
variable (Hlam : ∀ x T,
         (t : Term) →
         motive t →
         motive (lam x T t))

-- #eval Lean.Meta.getUnfoldEqnFor? ``fvar._def
-- #check app._unlock

opaque def rec (t : Term) : motive t := by
let motive' (t' : Impl.Term) := motive (cast Term._unlock.symm t')
rw [← cast_cast Term._unlock.symm Term._unlock t]
revert Hvar Happ Hplus Hite Hlam
rw [fvar._unlock, app._unlock, plus._unlock, ite._unlock, lam._unlock]
simp [fvar._def, app._def, plus._def, ite._def, lam._def]
intros Hvar Happ Hplus Hite Hlam
apply Impl.rec (motive := motive') <;> intros
<;> simp
next => apply Hvar
next h₀ h₁ =>
  specialize Happ _ _ h₀ h₁
  simp only [cast_cast] at Happ
  apply Happ
next h₀ h₁ =>
  specialize Hplus _ _ h₀ h₁
  simp only [cast_cast] at Hplus
  apply Hplus
next hc h₀ h₁ =>
  specialize Hite _ _ _ hc h₀ h₁
  simp only [cast_cast] at Hite
  apply Hite
next h₀ =>
  specialize Hlam _ _ _ h₀
  simp only [cast_cast] at Hlam
  apply Hlam

-- #exit
-- next =>
--   simp; rw [cast_app'']
--   generalize hk : cast _ _ = k
--   have ← : fvar = k := by rw [← hk, fvar._unlock]; rfl
--   auto
-- next =>
--   simp; rw [cast_app' Term._unlock]
--   -- generalize hk : cast _ _ = k
--   -- have ← : fvar = k := by rw [← hk, fvar._unlock]; rfl
--   -- auto

-- -- refine (cast )


-- -- rw [Term._unlock] at t


end rec

end Term
