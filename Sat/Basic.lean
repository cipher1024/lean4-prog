
import Lean
import Lean.Meta
import Std.Data.HashMap
import Std.Data.HashSet

open Std

namespace List

def toHashSet {α} [BEq α] [Hashable α] (xs : List α) : HashSet α :=
xs.foldl HashSet.insert HashSet.empty

end List

namespace AssocList
open Std.AssocList Ordering

-- variable {α β : Type u}
variable (cmp : α → α → Ordering)

def insert (k : α) (v : β) : AssocList α β → AssocList α β
| nil => cons k v nil
| cons k' v' xs =>
  if cmp k k' == lt then
    cons k v $ cons k' v' xs
  else
    cons k' v' (insert k v xs)

def sort : AssocList α β -> AssocList α β
| nil => nil
| cons k v xs => insert cmp k v (sort xs)

end AssocList


namespace List
open Std.AssocList Ordering

-- variable {α β : Type u}
variable (cmp : α → α → Ordering)

def insert (k : α) : List α → List α
| nil => [k]
| k' :: xs =>
  if cmp k k' == Ordering.lt then
    k :: k' :: xs
  else
    k' :: insert k xs

def sort : List α → List α
| nil => nil
| k :: xs => insert cmp k (sort xs)

@[specialize]
protected def compare : List α → List α → Ordering
| [], [] => eq
| [], x :: xs => Ordering.lt
| x :: xs, [] => gt
| x :: xs, y :: ys =>
  let hd := cmp x y
  if hd == eq then List.compare xs ys
  else hd

instance [Ord α] : Ord (List α) where
  compare := List.compare compare

end List

namespace Std
-- namespace HashMapBucket

-- protected def map (f : β → β') :
--   HashMapBucket α β → HashMapBucket α β'
-- | ⟨ar, har⟩ => ⟨ar.map $ AssocList.mapVal f, by simp [Array.map] ⟩

-- end HashMapBucket
-- namespace HashMapImp
-- end HashMapImp
namespace HashMap

instance {α β} [BEq α] [Hashable α] [BEq β] :
    BEq (HashMap α β) where
  beq x y :=
     x.size == y.size &&
     x.fold (λ b k v => b && y.find? k == some v) true

variable [BEq κ] [Hashable κ]

protected def map (f : α → β) (m : HashMap κ α) : HashMap κ β :=
m.fold (λ m' k x => m'.insert k (f x)) {}

end HashMap

namespace HashSet

instance [BEq α] [Hashable α] :
    BEq (HashSet α) where
  beq x y :=
     x.size == y.size &&
     x.fold (λ b k => b && y.contains k) true

instance [Ord α] [BEq α] [Hashable α] :
    Hashable (HashSet α) where
  hash c :=
   let m := c.val.buckets.val.map (List.sort compare)
   let m := m.map ( List.foldl (λ acc k => mixHash acc (hash k)) 0)
   m.foldl mixHash 0

end HashSet

end Std

structure Clause where
mkClauseImpl ::
  atoms : HashMap Nat Bool
  hashCode : UInt64

namespace ClauseImpl

def hashCode (c : HashMap Nat Bool) : UInt64 :=
 let m := c.val.buckets.val.map (AssocList.sort compare)
 let m := m.map ( AssocList.foldl (λ acc k v => mixHash acc (hash (k, v))) 0)
 m.foldl mixHash 0

instance : Hashable Clause where
  hash := Clause.hashCode

instance : BEq Clause where
  beq x y := x.atoms == y.atoms

end ClauseImpl

namespace Clause

protected def mk (c : HashMap Nat Bool) : Clause :=
{ atoms := c,
  hashCode := ClauseImpl.hashCode c }

open Ordering

instance [Ord α] [Ord β] : Ord (α × β) where
  compare
   | ⟨x₀, x₁⟩, ⟨y₀, y₁⟩ =>
     let r := compare x₀ y₀
     if r == eq
       then compare x₁ y₁
       else r

instance : Ord Clause where
  compare x y :=
    match compare (hash x) (hash y) with
    | lt => lt
    | gt => gt
    | eq => compare x.atoms.toList y.atoms.toList

end Clause

abbrev CNF := HashSet Clause

structure SmtState where
mkImpl ::
  vars : Std.HashMap Lean.Expr Nat := {}
  clauses : Std.HashMap Lean.Expr CNF := {}
  defs : Std.HashMap CNF Nat := {}

def SmtState.mk : SmtState :=
{}
-- { vars := {},
--   clauses := {},
--   defs := {} }

open Lean (MetaM Expr)
open Lean.Expr

abbrev SmtM := StateT SmtState MetaM

def unitClause (v : Nat) (b : Bool) : Clause :=
  Clause.mk $ HashMap.empty.insert v b

def mkLit (i : Nat) : CNF :=
  HashSet.empty.insert
    $ unitClause i true

def Clause.negate (c : Clause) : CNF :=
  let x := c.atoms.toList
  x.foldl (λ s ⟨v,b⟩ => s.insert $ unitClause v !b) HashSet.empty

def Clause.join (c₀ c₁ : Clause) : OptionM Clause :=
let f c v b :=
  match c.find? v with
  | some b' =>
    if b == b' then some c
    else none
  | none => some $ c.insert v b
Clause.mk <$> c₀.atoms.foldM f HashMap.empty

def Lit.toString (v : Nat) : Bool -> String
| true => s!"x{v}"
| false => s!"¬ x{v}"
-- | false => "¬ x" ++ toString v

def Clause.toStringAux : List (Nat × Bool) → String
| [] => "false"
| [(v, b)] => Lit.toString v b
| (v, b) :: vs => Lit.toString v b ++ " ∨ " ++ toStringAux vs

def Clause.toString (c : Clause) : String :=
  let xs := c.atoms.toList
  let r := Clause.toStringAux xs
  if c.atoms.size > 1 then s!"({r})"
  else r

namespace CNF

def true : CNF :=
HashSet.empty.insert $ Clause.mk HashMap.empty

def false : CNF :=
HashSet.empty

open List (mapM)
-- #print notation |>.

protected def toString (f : CNF) : String :=
if f.isEmpty
  then "true"
  else String.intercalate " ∧ " (f.toList.map Clause.toString)

instance : ToString CNF where
  toString := CNF.toString

def mkAnd' (f₀ f₁ : CNF) : CNF :=
  f₀.fold HashSet.insert f₁

def mkDefStmt (v : Nat) (f : CNF) : CNF :=
  let f₀ : CNF := f.fold (λ f c =>
    f.insert $ Clause.mk $ c.atoms.insert v Bool.false) {}
  let f₁ : CNF := f.fold (λ f c =>
    f.insert $ Clause.mk $ c.atoms.map not |>.insert v Bool.true) {}
  mkAnd' f₀ f₁

def mkDef (f : CNF) : SmtM Nat := do
  let s ← get;
  match s.defs.find? f with
  | some v => return v
  | none => do
    let v := s.vars.size + s.defs.size
    set { s with defs := s.defs.insert f v }
    return v

def mkAnd (f₀ f₁ : CNF) : SmtM CNF :=
  return mkAnd' f₀ f₁

def mkOr (f₀ f₁ : CNF) : SmtM CNF := do
  let d ← mkDef f₁
  return f₀.fold (λ ϕ c =>
    ϕ.insert $ Clause.mk $
      c.atoms.insert d Bool.true) {}

def mkNot (f₀ : CNF) : SmtM CNF :=
  let f₁ := f₀.toList.map Clause.negate
  f₁.foldlM mkOr false

def mkImplies (f₀ f₁ : CNF) : SmtM CNF := do
  mkOr (← mkNot f₀) f₁

def mkIff (f₀ f₁ : CNF) : SmtM CNF := do
  mkAnd (← mkImplies f₀ f₁) (← mkImplies f₁ f₀)

def mkVar (e : Expr) : SmtM CNF := do
  let s ← get;
  match s.vars.find? e with
  | some i => return (mkLit i)
  | none =>
    let i := s.vars.size + s.defs.size
    set { s with vars := s.vars.insert e i }
    return (mkLit i)

def internalize (e : Lean.Expr) : SmtM CNF := do
  let s ← get;
  match s.clauses.find? e with
  | some ϕ => return ϕ
  | none =>
    let f ←
      match e with
      | app (app f x _) y _ =>
        if f.isConstOf ``And
          then mkAnd (← internalize x) (← internalize y)
        else if f.isConstOf ``Or
          then mkOr (← internalize x) (← internalize y)
        else if f.isConstOf ``Iff
          then mkIff (← internalize x) (← internalize y)
        else mkVar e
      | app f x _ =>
        if f.isConstOf ``Not
          then mkNot (← internalize x)
          else mkVar e
      | forallE _ d b _ =>
        let td ← liftM $ Lean.Meta.inferType d
        let tb ← liftM $ Lean.Meta.inferType b
        if td.isProp && tb.isProp
          then mkImplies (← internalize d) (← internalize b)
          else mkVar e
      | _ => mkVar e
    modify $ λ s => { s with clauses := s.clauses.insert e f }
    return f

def runSmtM (m : SmtM α) : MetaM α :=
  StateT.run' m {}

def evalSmtM (m : SmtM CNF) : MetaM CNF := do
  let ⟨x, s⟩ ← StateT.run m {}
  return s.defs.fold (λ ϕ d v => mkAnd' ϕ (mkDefStmt v d)) x

-- def smt (e : CNF -> SmtM Unit) : MetaM Unit := do

open Lean Meta
open Lean Elab Elab.Tactic PrettyPrinter Meta

-- #check Meta.Context

-- structure Filtered (m : Type u → Type u) (ρ : Type u) (α : Type u) where
-- filtered ::
--   pred : α → m (ULift Bool)
--   collection : ρ

-- instance (m : Type u → Type u) (ρ : Type u) (α : Type u) [ForIn m ρ α] :
--     ForIn m (Filtered m ρ α) α where
--   forIn

def getPropAsms : TacticM (List LocalDecl) := do
  let lctx ← getLCtx
  lctx.fvarIdToDecl.foldlM (λ acc id decl => do
           let t ← inferType (← inferType (mkFVar id))
           if t.isProp ∧ ¬ decl.isAuxDecl
             then return decl :: acc
             else acc ) []

instance : Repr LocalDecl where
  reprPrec x _ :=
    let val :=
      match x.value? with
      | some e => s!" := {e}"
      | none => ""
    s!"({x.fvarId.name}) {x.userName} {x.isAuxDecl}" ++ val

def myTac : TacticM Unit := do
  let lctx ← getPropAsms
  let ⟨vs,g⟩ ← liftMetaM $ revert (← getMainGoal) (List.toArray $ lctx.map LocalDecl.fvarId)
  replaceMainGoal [g]
  let p ← getMainTarget
  let c ← evalSmtM (internalize p)
  IO.println p
  IO.println c
  -- let g ← getMainGoal
  -- IO.println g
  -- let r ← liftMetaM read
  -- let lctx ← getLCtx
  -- IO.println $ repr lctx.fvarIdToDecl.toList
  -- IO.println (← getMainTag)
  -- let d ← getMainDecl
  -- IO.println d.userName
  -- let lctx ← getPropAsms
  -- IO.println $ repr lctx
  -- for x in lctx do
  --   IO.println x.userName
  --   let t ← inferType $ mkFVar x.fvarId
  --   IO.println t
  --   let t ← inferType t
  --   IO.println t


elab "myTac" : tactic => do myTac

-- macro "myTac" : tactic => `(CNF.myTac)

end CNF

-- open Tactic

-- namespace Mathlib.Tactic.Ext

-- theorem foo (p q r : Prop) (h : r ∨ q) :
--   p ∧ q ∨ r :=
-- by { myTac }

theorem foo' (p q r : Prop) :
  p ∧ ¬ q ∨ q :=
by { myTac; admit }

-- #check 3
