
import Lib.Data.Nat
import Lib.Meta.Opaque

namespace Fin
open Nat
protected def succ {n} : Fin n → Fin (succ n)
| ⟨i,h⟩ => ⟨i.succ, Nat.succ_lt_succ h⟩

def widen {n} : Fin n → Fin (succ n)
| ⟨i,h⟩ => ⟨i, Nat.lt_succ_of_le <| Nat.le_of_lt h⟩

end Fin


inductive Typ : Type
| nat | bool | arrow (t₀ t₁ : Typ)

open Nat
inductive Term' : Nat → Type
| bvar {n} : Fin n → Term' n
| fvar {n} : String → Term' n
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

def subst (v : String) (e : Term' n) : Term' n → Term' n
| bvar i => bvar i
| fvar v' =>
  if v = v' then e else fvar v'
| plus t₀ t₁ => plus (subst v e t₀) (subst v e t₁)
| Term'.ite c t₀ t₁ =>
  ite (subst v e c) (subst v e t₀) (subst v e t₁)
| app t₀ t₁ => app (subst v e t₀) (subst v e t₁)
| lam T t' => lam T (subst v (bump 0 e) t')

inductive Occurs : {n : Nat} → String → Term' n → Prop
| fvar : Occurs (n := n) v (fvar v)
| plus₀ {t₀ t₁ : Term' n} : Occurs v t₀ → Occurs v (plus t₀ t₁)
| plus₁ {t₀ t₁ : Term' n} : Occurs v t₁ → Occurs v (plus t₀ t₁)
| ite_c {c t₀ t₁ : Term' n} : Occurs v c → Occurs v (ite c t₀ t₁)
| ite₀ {c t₀ t₁ : Term' n} : Occurs v t₀ → Occurs v (ite c t₀ t₁)
| ite₁ {c t₀ t₁ : Term' n} : Occurs v t₁ → Occurs v (ite c t₀ t₁)
| app₀ {t₀ t₁ : Term' n} : Occurs v t₀ → Occurs v (app t₀ t₁)
| app₁ {t₀ t₁ : Term' n} : Occurs v t₁ → Occurs v (app t₀ t₁)
| lam {T} {t : Term' (succ n)} : Occurs v t → Occurs v (lam T t)

def fresh' (n : Nat) : Term' k → Nat
| fvar v =>
  match String.toNat? <| v.drop 1 with
  | none => n
  | some n' => max n (n' + 1)
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

def fresh (t : Term' n) : String :=
"x" ++ toString (fresh' 0 t)

theorem le_fresh' (t : Term' k)
  (h : m ≤ n) :
  m ≤ fresh' n t := by
induction t generalizing n
<;> simp [fresh', *]
next =>
  split
  next => auto
  next => auto [Nat.le_max_l]
next ihc ih₀ ih₁ => auto
  -- -- next => auto
  -- apply ih₁
  -- apply ih₀
  -- apply ihc


theorem not_Occurs_fresh (t : Term' n) :
  ¬ Occurs (fresh t) t := by
suffices ∀ k n : Nat, Occurs ("x" ++ toString n) t → n < fresh' k t by
  intro h; specialize this 0 _ h
  apply Nat.lt_irrefl _ this
-- suffices ∀ k n : Nat, k ≤ n → Occurs ("x" ++ toString n) t → n < fresh' k t by
  -- intro h; specialize this 0 _ (Nat.zero_le _) h
  -- apply Nat.lt_irrefl _ this

intros m k
-- intros m k h₀
generalize hv : "x" ++ toString k = v; intros h
induction h generalizing m
<;> simp [fresh']
next v' =>
  have : String.toNat? (String.drop v' 1) = some k := by
    rw [← hv]
  simp [this]
  auto
next ih =>
  auto [le_fresh']
next ih =>
  apply ih _ hv
next =>
  auto [le_fresh']
  -- split

end Term'

def Term := Term' 0

namespace Term

export Term' (subst fvar plus ite app)
open Term'

-- opaque
def lam (x : String) (T : Typ) (t : Term) : Term :=
Term'.lam T (t.bump 0 |>.subst x <| bvar 0)

open Term in
inductive View : Term → Type
| fvar {x} : View (fvar x)
| plus {t₀ t₁} : View t₀ → View t₁ → View (plus t₀ t₁)
| ite {c t₀ t₁} : View c → View t₀ → View t₁ → View (Term.ite c t₀ t₁)
| app {t₀ t₁} : View t₀ → View t₁ → View (app t₀ t₁)
| lam {x T t} : View t → View (lam x T t)

end Term
