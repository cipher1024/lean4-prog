
import Lib.Meta
import Lib.Tactic

namespace Lean.Elab.Tactic

open Lean.Elab.Tactic
open Lean Lean.Meta
open Lean.Elab
open Lean.Elab.Term
open Lean.PrettyPrinter.Delaborator.TopDownAnalyze
open Lean.Elab.Tactic

-- initialize registerTrace
initialize registerTraceClass `select.match.failure
initialize registerTraceClass `select.match.attempt
initialize registerTraceClass `select.match.success
initialize registerTraceClass `select.skipped

inductive Selector where
  | hyp (name : Name) (pattern : Expr)
  | goal (pattern : Expr)

def headZeta1 : Expr → Expr
| .mdata _ e _ => headZeta1 e
| .letE v t e e' _ => instantiateBVar [e] e'
| e => e

def clearLDecl (l : LocalDecl) : TacticM (Array Name) :=
withMainContext do
  -- println!"before"
  -- print_vars![mainGoal]
  let some l' ← tryTactic? <| liftMetaTactic1' (revert . #[l.fvarId])
    | pure #[]
  -- println!"reverted"
  let tgt ← getMainTarget
  -- println!"main target"
  liftMetaTactic1 (change . <| headZeta1 tgt)
  let l' := l'[1:].toArray
  -- println!"after"
  l'.mapM (λ v => do return (← getLocalDecl v).userName)

open Lean (Meta.ppExpr)
open Lean.Meta (ppExpr)

def elabHypSelector : Selector → SearchTacticM δ (Option (LocalDecl × LocalDecl))
| .hyp tag pat => do
  let lctx ← getLCtx
  let ls := λ _ : Unit =>
    lctx.decls.toList.filterMap <| Option.map (·.userName)
  let some h := (← SearchT.pick lctx.decls.toList) | failure
  trace[select.match.attempt]" trying {h.userName} with {← Meta.ppExpr pat}"
  unless ¬ h.isAuxDecl do
    trace[select.skipped]"skipping {h.userName} ({h.fvarId.name}) "
    failure
  let t := h.type
  unless (← liftM <| isDefEqAssigning t pat) do
    trace[select.match.failure]" tried {h.userName} with {← Meta.ppExpr pat}"
    failure
  trace[select.match.success]" tried {h.userName} with {← Meta.ppExpr pat}"
  liftMetaTactic1 (define . tag h.type <| mkFVar h.fvarId)
  let var ← liftMetaTactic1' (intro . tag)
  let var ← withMainContext (getLocalDecl var)
  return some (var, h)
| .goal pat => do
  let g ← getMainTarget
  unless (← liftM <| isDefEqAssigning g pat) do
    trace[select.match.failure]" tried goal with {← Meta.ppExpr pat}"
    failure
  return none

-- #exit

def elabHypSelectors (sel : Array Selector) (tac : Option Syntax) :
  SearchTacticM δ (Array (LocalDecl × LocalDecl)) := do
let mappings ← sel.filterMapM elabHypSelector
match tac with
| none => pure ()
| some tac => evalTactic tac
return mappings

def elabSelectors (sel : Array Selector) (tac : Option Syntax) :
  TacticM (Array (LocalDecl × LocalDecl)) := do
elabHypSelectors sel tac |>.run


declare_syntax_cat asm_select
declare_syntax_cat asm_selectors

syntax (name := hyp_selector)
  colGt withPosition("hyp " ident " : " colGt term) ppLine : asm_select
syntax (name := goal_selector)
  colGt withPosition("goal " " : " colGt term) ppLine : asm_select
syntax (name := many_selectors) (asm_select)+ : asm_selectors
syntax (name := one_selector) group(ident " : " colGt term) : asm_selectors

syntax withPosition("select " asm_selectors (colGt tacticSeq)?) : tactic

elab "have! " d:haveDecl : tactic => do
  let Hid := d[0][0][0].getId
  let decl ← getLocalDeclFromUserName Hid
  evalTactic (← `(tactic| have $d:haveDecl))
  liftMetaTactic1 (clear . decl.fvarId)

elab "have? " d:haveDecl : tactic => do
  evalTactic (← `(tactic| have $d:haveDecl))
  let Hid := d[0][0][0].getId
  withMainContext do
  let ldecl ← getLocalDeclFromUserName Hid
  for h in ← getLCtx do
    if h.fvarId != ldecl.fvarId && (← isDefEq h.type ldecl.type) then
      throwError "Local decl {h.userName} already has type {ldecl.type}"

def parseSelector (xs : Syntax) : TacticM (Array Selector) := do
if xs.getKind == ``one_selector then
  let xs := xs[0]
  let tag := xs[0].getId
  let colon := xs[1]
  let term := xs[2]
  let pat ← Term.elabTerm term none
  return #[ Selector.hyp tag pat ]
else
  let mut r := #[]
  for x in xs[0].getArgs do
    if x.getKind == ``goal_selector then
      let kw    := x[0]
      let colon := x[1]
      let term  := x[2]
      let pat ← Term.elabTerm term none
      r := r.push <| Selector.goal pat
    else
      let kw    := x[0]
      let tag   := x[1].getId
      let colon := x[2]
      let term  := x[3]
      let pat ← Term.elabTerm term none
      r := r.push <| Selector.hyp tag pat
  return r

elab_rules : tactic
| `(tactic| select $xs $[$tac:tacticSeq]?) =>
Lean.MonadQuotation.withFreshMacroScope do
withMainContext do
    let sels ← parseSelector xs
    let hs ← elabSelectors sels tac
    if tac.isSome then
      withMainContext do
      let mut vs := #[]
      for (v, _) in hs.reverse do
        let vs' ← clearLDecl v
        vs := vs ++ vs'.reverse
      withMainContext do
      for v in vs.reverse do
        discard <| liftMetaTactic1' (intro . v)


example (a b c x y z : Nat)
  (a₀ : a ≤ b)
  (a₁ : b ≤ c)
  (h₁ : y ≤ z)
  (h₂ : x ≤ z)
  (h₀ : x ≤ y)
  -- (hh : x ≤ w)
  (h₃ : z ≤ w)
 : x ≤ w := by
-- repeat
repeat
  select
    hyp h : ?x ≤ ?y
    hyp h' : ?y ≤ ?z
    -- goal : ?x ≤ ?z
    have? h₃ := Nat.le_trans h h'
skip
admit
-- have : h = h := rfl
-- have : h' = h' := rfl
  -- clear h
  -- revert h'
  -- have? h₄ := rfl
-- intro
-- select h'' : _ ≤ ?x

-- skip
