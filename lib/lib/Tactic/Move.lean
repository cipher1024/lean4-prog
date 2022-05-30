
import Lib.Meta
import Lib.Tactic

namespace Lean.Elab.Tactic

open Lean.Elab.Tactic
open Lean Lean.Meta
open Lean.Elab
open Lean.Elab.Term
open Lean.PrettyPrinter.Delaborator.TopDownAnalyze
open Lean.Elab.Tactic

declare_syntax_cat move_intro_pat
declare_syntax_cat move_revert_pat
syntax tactic colGt " => " (colGt move_intro_pat)+ : tactic

-- #exit

syntax (name := skip) "_" : move_intro_pat
syntax (name := auto) "//" : move_intro_pat
syntax (name := simp) "/=" : move_intro_pat
syntax (name := autoSimp) "//=" : move_intro_pat
syntax (name := introIdent) ident : move_intro_pat
syntax (name := apply) "/" group(ident <|>  ("(" term ")")) : move_intro_pat
-- syntax (name := applyTerm) "/" "(" term ")" : move_intro_pat
syntax (name := casePat) "[" sepBy(move_intro_pat*, "|", " | ")  "]" : move_intro_pat

syntax (name := revertIdent) ident : move_revert_pat
syntax (name := revertGen) (group(("!")? "(" term ")") <|> group("!" ident)) : move_revert_pat

-- TODO: clear pattern, `_`, `?` patterns
-- TODO: using intro patterns with `have`

-- #exit

-- syntax "move" : tactic
-- syntax withPosition("move" ":" (colGt move_revert_pat)+) : tactic

-- #exit

inductive MoveIntroPat where
-- | auto (ref : Syntax)
-- | simp (ref : Syntax)
| autoSimp (ref : Syntax) (simp auto : Bool := true)
| intro (ref : Syntax) (n : Name)
| apply (e : Syntax)
| case (opS clS : Syntax) (brs : Array (Array MoveIntroPat))
deriving Repr, Inhabited, BEq -- , DecidableEq

def MoveIntroPat.auto (ref : Syntax) : MoveIntroPat :=
.autoSimp ref false true

def MoveIntroPat.simp (ref : Syntax) : MoveIntroPat :=
.autoSimp ref true false

mutual

partial def parseMoveIntroPat (pat : Syntax) : TacticM MoveIntroPat := do
if pat.getKind == ``skip then
  return .intro pat `_
else if pat.getKind == ``introIdent then
  return .intro pat pat[0].getId
else if pat.getKind == ``auto then
  return .auto pat
else if pat.getKind == ``simp then
  return .simp pat
else if pat.getKind == ``autoSimp then
  return .autoSimp pat
else if pat.getKind == ``apply then
  let fn := pat[1]
  if pat[1].getNumArgs == 1 then
    return .apply pat[1][0]
  if pat[1].getNumArgs == 3 then
    return .apply pat[1][1]
else if pat.getKind == ``casePat then
  return .case pat[0] pat[2] (← pat[1].getArgs.getSepElems.mapM parseMoveIntroPatArray)
throwIllFormedSyntax

partial def parseMoveIntroPatArray (pat : Syntax) :
  TacticM (Array MoveIntroPat) := do
pat.getArgs.mapM parseMoveIntroPat

end


/-

6 2 1 0 0 0 1 0 0 0
0 1 2 3 4 5 6 7 8 9

-/
-- #exit

def runintro (ref : Syntax) (n : Name) : TacticM Unit :=
  withTacticInfoContext ref <|
    discard <| liftMetaTactic1' (intro . n)

-- #fullname auto
-- #check Lean.Elab.Tactic.auto
-- #check autoTac

partial def runMoveIntroPat : MoveIntroPat → TacticM Unit
| .intro ref n =>
  -- runintro ref n
  withTacticInfoContext ref <|
    discard <| liftMetaTactic1' (intro . n)
| .case opBrack clBrack pats => do
  withTacticInfoContext opBrack (pure ())
  liftMetaTactic λ g => do
    let (v, g) ← intro1 g
    let gs ← cases g v
    -- let mut gs' := #[]
    unless pats.size == gs.size ||
           (pats == #[#[]]) do
      throwError "mismatched numbers of branches and patterns"
    gs.toList.mapM λ ⟨g, p⟩ => do
      let vs := g.fields.map (·.fvarId!)
      let g  := g.mvarId
      (·.2) <$> revert g vs
  let gs ← getGoals
  let gs' ← gs.zip pats.toList |>.mapM λ ⟨g,ps⟩ => do
    setGoals [g]
    for p in ps do
      allGoals <| runMoveIntroPat p
    getGoals
  setGoals gs'.join
  withTacticInfoContext clBrack (pure ())
| .apply rule =>
  withTacticInfoContext rule <|
  liftMetaTactic1' λ g => do
    let (v, g) ← intro1 g
    let rule ← Term.elabTerm rule none |>.run'
    withMVarContext g do
    let pr  ← mkAppM' rule #[mkFVar v]
    let typ ← inferType pr
    let g ← assert g `h typ pr
    let g ← clear g v
    return ((), g)
-- | .auto ref =>
| .autoSimp ref callSimp callAuto => do
  -- let stx ← `(tactic| simp)
  if callSimp then
    withTacticInfoContext ref <|
      liftMetaTactic1 (simpTarget . {})
  if callAuto then
    withTacticInfoContext ref autoTac
    -- evalTactic (← `(tactic| try auto))
-- | _ => throwError "foo"


-- #check Lean.Elab.Tactic.simp
-- #check Lean.Meta.Simp.simp

-- partial def runMoveIntroPat : MoveIntroPat → TacticM Unit
-- | .intro ref n => runintro ref n
--   -- withTacticInfoContext ref <|
--     -- discard <| liftMetaTactic1' (intro . n)
-- | .case opBrack clBrack pats => do
--   withTacticInfoContext opBrack (pure ())
--   liftMetaTactic λ g => do
--     let (v, g) ← intro1 g
--     let gs ← cases g v
--     -- let mut gs' := #[]
--     unless pats.size == gs.size ||
--            (pats == #[#[]]) do
--       throwError "mismatched numbers of branches and patterns"
--     gs.toList.mapM λ g => do
--       let vs := g.fields.map (·.fvarId!)
--       let g  := g.mvarId
--       (·.2) <$> revert g vs
--   withTacticInfoContext clBrack (pure ())
--   -- sorry
-- -- | .apply rule =>
-- --   withTacticInfoContext rule <|
-- --   liftMetaTactic1' λ g => do
-- --     let (v, g) ← intro1 g
-- --     let rule ← Term.elabTerm rule none |>.run'
-- --     withMVarContext g do
-- --     let pr  ← mkAppM' rule #[mkFVar v]
-- --     let typ ← inferType pr
-- --     let g ← assert g `h typ pr
-- --     let g ← clear g v
-- --     return ((), g)
-- -- | .simp ref => do
-- --   -- let stx ← `(tactic| simp)
-- --   withTacticInfoContext ref do
-- --     Elab.Tactic.simp
-- -- | .auto ref =>
-- --   withTacticInfoContext ref do
-- --     evalTactic (← `(tactic| try auto))
-- -- | .autoSimp ref => sorry
-- --   -- withTacticInfoContext ref do
-- --     -- evalTactic (← `(tactic| simp; try auto))
-- | _ => throwError "foo"

-- #synth BEq Syntax
-- #print Syntax.instBEqSyntax

inductive MoveRevertPat where
  | revert (ref : Syntax) (n : Name)
  | generalize (ref : Syntax) (n : Bool) (t : Syntax)
deriving Repr, BEq

-- #check BEq

-- #exit

-- #check SepArray.getSepElems
def parseMoveRevertPat (s : Syntax) : TacticM MoveRevertPat := do
if s.getKind == ``revertIdent then
  return .revert s s[0].getId
else if s.getKind == ``revertGen then
  -- let tag :=
  --   if
  --     then none
  --     else some s[0][0].getId
  let term :=
    if s[0].getKind == groupKind
      then s[0][2]
      else s[0]
  return .generalize s (s[0].getNumArgs != 0) term
throwError "invalid revert pattern {s} ({s.getKind}, {s.getArgs})"

def MoveRevertPat.toRef : MoveRevertPat → Syntax
| .revert ref n => ref
| .generalize ref _ _ => ref

def runMoveRevertPat : MoveRevertPat → TacticM Unit
| .revert ref n =>
withMainContext do
-- withTacticInfoContext ref <| do
  let v ← getLocalDeclFromUserName n
  discard <| liftMetaTactic1' (revert . #[v.fvarId])
| .generalize ref h e =>
withMainContext do
-- withTacticInfoContext ref <| do
  -- print_vars![mainGoal, e]
  let e ← elabTerm e none
  let h := if h then some `h else none
  print_vars![mainGoal, e]
  let vs ← liftMetaTactic1' (generalize .
    #[ { expr := e, hName? := h, xName? := some `x }])
  withMainContext do
  discard <| liftMetaTactic1' (revert . vs.reverse)

-- #eval "A"
-- #exit

-- macro_rules
-- | `(tactic| move ) => `(tactic| skip)

-- #eval "A"

declare_syntax_cat revert_pats

-- #eval "A"

syntax ":" (colGt move_revert_pat)+ : revert_pats
-- #eval "A"

syntax "move" (colGt revert_pats)?  : tactic

elab_rules : tactic
| `(tactic| move%$token $[$xs:revert_pats]? ) => do
match xs with
| some xs =>
  let colon := xs[0]
  let xs := xs[1].getArgs
  withTacticInfoContext (mkNullNode #[token, colon]) (pure ())
  for x in xs.reverse do
    let x' ← parseMoveRevertPat x
    runMoveRevertPat x'
| none => return ()
  -- println!"{}"
  -- xs.reverse.forM runMoveRevertPat

-- #eval "B"
-- #exit

elab_rules : tactic
| `(tactic| $tac => $pats*) => do
  -- let pats' ← pats.mapM parseMoveIntroPat
  evalTactic tac
  let arrow := (← getRef)[1]
  withTacticInfoContext arrow (pure ())
  for pat in pats do
    let pat' ← parseMoveIntroPat pat
    -- let next := pats.getD (i+1) Syntax.missing
    allGoals <| runMoveIntroPat pat'
  -- println!"repr: {repr xs}"
-- #check [1:3]
-- #check Std.Range

-- move => a b c
--        ^
-- -- ⊢ T → V → U → True
-- move => a b c
--          ^
-- ⊢ T → V → U → True

-- u : T
-- ⊢ V → U → True


-- example : True := by
-- let T := True
-- let U := True
-- let V := True
-- -- have h₀ : T ↔ U := sorry
-- -- have h₁ : U ↔ V := sorry
-- have t : T := True.intro
-- have v : V := True.intro
-- have u : U := True.intro
-- have x : Nat × Nat := sorry
-- have y : List Nat ⊕ List Nat := sorry
-- -- revert e
-- -- rewrite [h₀, h₁]
-- have f : T → U := id
-- -- move: t u v => /f u v t
-- -- have' h : T ⊕' U := sorry
-- -- move: !(T ⊕' U) h
-- move: t u v y x
-- move => v u t
-- move => [ |] ys [ x y ] ;
-- -- move => [ x y ]
-- -- move => [ xs |]
-- skip
-- -- move: f h:(f) => y x
-- -- move => /f d // ;


end Lean.Elab.Tactic

-- Local Variables:
-- lean4-test-file: "/Users/simon/google stuff/lean/sat/concrete-semantics/ConcreteSemantics/ch7.lean"
-- End:
