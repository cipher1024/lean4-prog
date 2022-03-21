
-- import Lib.Data.Array.Instances
import Lean.Parser
import Lean.Elab.Command
import Lean.Meta.Constructions
import Std.Data.HashMap
import Lean.Elab.Tactic.BuiltinTactic
import Lean.Elab.Tactic.Conv.Basic

import Lib.Meta
import Lib.Meta.ImportPrivate
import Lib.Meta.DeclGraph
import Lib.Tactic

open Lean (Name)

inductive RuleToken' (tok var : Type)
| var (n : var)
| tok (n : tok)
deriving Repr

namespace RuleToken'

@[specialize]
def mapM [Monad m] (f : α → m β) (g : α' → m β') :
  RuleToken' α α' → m (RuleToken' β β')
| var v => do let v' ← g v; return var v'
| tok v => do let v' ← f v; return tok v'

@[specialize]
def mapM₁ [Monad m] (f : α → m β) : RuleToken' α α' → m (RuleToken' β α') :=
mapM f pure

@[specialize]
def mapM₂ [Monad m] (f : α' → m β') : RuleToken' α α' → m (RuleToken' α β') :=
mapM pure f

end RuleToken'

def RuleToken := RuleToken' Name

structure Rule' (α β : Type) where
  head : β
  prod : Array (RuleToken' α β)
deriving Repr

namespace Rule'

@[specialize]
def mapM [Monad m] (f : α → m β) (g : α' → m β')
  (x : Rule' α α') : m (Rule' β β') := do
let hd' ← g x.head
let prod' ← x.prod.mapM (·.mapM f g)
return { head := hd', prod := prod' }

end Rule'

def Rule := Rule' String Name

abbrev Production := Array (RuleToken' Name Nat)
abbrev SyntCat := Name × Array Production

open Std

structure Grammar where
  tokens : HashMap Name String := {}
  rules : Array SyntCat := #[]
-- #check Repr
instance : Repr Grammar where
  reprPrec x n :=
    s!"\n\{ tokens := {repr x.tokens.toList}\n  rules := {repr x.rules} }"

structure GrammarBuilder extends Grammar where
  vars : HashMap Name Nat := {}
  tokens' : HashMap Name Nat := {}
  lexemes : HashMap String Name := {}

abbrev M := StateM GrammarBuilder

def M.run (x : M α) : α :=
x.run' {}

-- #check Lean.Syntax.mkNameLit

def mkToken (tok : String) : M Name := do
let s ← get
if let some t := s.lexemes.find? tok then return t
else
  let tok' := tok.trim.takeWhile Char.isAlpha
  let tok' := Name.mkSimple <| if tok' == "" then "tok_" ++ tok else tok'
  if let some i := s.tokens'.find? tok' then
    let tok'' := tok'.appendIndexAfter i
    set {s with
      tokens := s.tokens.insert tok'' tok
      tokens' := s.tokens'.insert tok' <| i + 1
      lexemes := s.lexemes.insert tok tok'' }
    return tok''
  else
    set {s with
      tokens := s.tokens.insert tok' tok
      tokens' := s.tokens'.insert tok' 0
      lexemes := s.lexemes.insert tok tok' }
    return tok'

def getIndex (v : Name) : M Nat := do
let s ← get
if let some i := s.vars.find? v then
  return i
else
  let i := s.rules.size
  set { s with
    vars := s.vars.insert v i,
    rules := s.rules.push (v, #[]) }
  return i

def pushProduction (v : Rule' Name Nat) : M Unit :=
modify λ s => { s with
  rules := s.rules.modify v.head (λ (n,a) => (n, a.push v.prod)) }

def mkGrammar (rules : Array Rule) : Grammar := M.run do
  for r in rules do
    pushProduction (← r.mapM mkToken getIndex)
  return (← get).toGrammar


syntax (name := inspectCatCmd) "#inspect_cat " ident : command
open Lean.Elab.Command
-- #check Lean.Elab.Command.CommandElab
open Lean Parser Elab Command

@[commandElab inspectCatCmd]
def elabInspectCat : CommandElab
| `(#inspect_cat%$kw $catId:ident) => do
  let catName := catId.getId
  let cats := parserExtension.getState (← getEnv) |>.categories
  match cats.find? catName with
  | some cat =>
    logInfoAt kw <| repr <| cat.tables.leadingTable.toList.map (·.1)
  | none =>
    logErrorAt catId s!"unknown category `{catName}`"
| _ => throwError "unsupported syntax"

structure LineInfo where
  line : Nat
  col : Nat

structure Token {t} (x : t) where
  begLoc : LineInfo
  lexeme : Substring
  endLoc : LineInfo

class IsToken (t : Type) where
  lexemeOf : t → String

structure ParserState where
  lineInfo : LineInfo
  cur : String.Iterator

def EStateM.Result.state : EStateM.Result ε σ α → σ
|  EStateM.Result.ok _ s .. => s
|  EStateM.Result.error _ s .. => s

structure ParserM (α : Type) where
  parser : EStateM String _root_.ParserState α
  mono : ∀ li (s : String.Iterator), s.pos ≤ (parser ⟨li, s⟩).state.cur.pos

instance : Monad ParserM where
  pure x := ⟨pure x, λ _ _ => Nat.le_refl _⟩
  bind x f :=
    { parser := x.parser >>= λ a => f a |>.parser,
      mono := λ li it =>
        Nat.le_trans (x.mono li it) $ by
          cases x; next p Hmono =>
          cases h₀ : p { lineInfo := li, cur := it }
            <;> simp [bind, EStateM.bind, h₀]
          next a b => apply f a |>.mono
          next => refl }

-- #print Alternative

def ParserM.failure : ParserM α where
  parser x := EStateM.Result.error "error" x
  mono li it := Nat.le_refl _

def ParserM.orElse (x : ParserM α) (f : Unit → ParserM α) : ParserM α where
  parser := x.parser <|> (f ()).parser
  mono li it := by
    simp [HOrElse.hOrElse, OrElse.orElse, EStateM.orElse]
    cases h : parser x { lineInfo := li, cur := it }
    next a b => simp [← h]; apply x.mono li it
    next a => cases a; next err a b =>
      simp [EStateM.Backtrackable.save, EStateM.dummySave,
            EStateM.Backtrackable.restore, EStateM.dummyRestore]
      apply Nat.le_trans _ <| (f ()).mono a b
      show it.pos ≤ (EStateM.Result.error (α := α) err { lineInfo := a, cur := b : _root_.ParserState }).state.cur.pos
      rw [← h]; apply ParserM.mono

instance : Alternative ParserM where
  failure := ParserM.failure
  orElse := ParserM.orElse

def Lexeme (T : Type) [IsToken T] := Σ t : T, Token t
def readToken [IsToken T] : ParserM (Lexeme T) := sorry
def getLineInfo : ParserM LineInfo := sorry
def readThisToken [IsToken T] (x : T) : ParserM (Token x) := sorry

-- def loop (f : α → ParserM β) :

-- def readChar : ParserM Char where
--   parser := _
--   mono := _

namespace Lean.Command
open Lean.Parser

declare_syntax_cat rules
declare_syntax_cat rule
declare_syntax_cat symbol
syntax (ident <|> strLit) : symbol
syntax ident withPosition(" ::= " (colGt symbol)*) : rule
syntax rule* : rules
syntax(name := grammarCmd) "grammar " ident rules "end " ident : command

open Lean.Syntax

def getTypeName (n n' : Name) : MetaM Name := do
let ns ← getCurrNamespace
if n == n'
then return ns ++ n
else return ns ++ n ++ n'

open Lean.Meta
-- #check CasesSubgoal

def declLexemeOf (n : Name) (g : Grammar) : MetaM Unit := do
let typeName ← getTypeName n `Token
let t ← mkArrow (mkConst typeName) (mkConst ``String)
let mv₀ ← mkFreshExprMVar t
let (v, mv) ← intro mv₀.mvarId! `x
let xs ← cases mv v
xs.forM λ c => do
  let lex := g.tokens.find! <| Name.mkSimple c.ctorName.getString!
  let e := mkStrLit lex
  assignExprMVar c.mvarId e
let e ← instantiateMVars mv₀
let n' ← getTypeName n `lexemeOf
-- addDecl <| Declaration.defnDecl ⟨_, e, ReducibilityHints.regular _, _⟩
discard <| addDef [] n' t e
let classT ← mkAppM ``IsToken #[mkConst typeName]
let instDef ← mkAppM ``IsToken.mk #[mkConst n']
let n' ← getTypeName n `instIsToken
discard <| addInst [] n' classT instDef
-- println!"name: {classT}"
-- println!"name: {instDef}"

  -- println!"ctor: {c.ctorName} {repr lex}"
-- _

def declTokenType (n : Name) (g : Grammar) : MetaM Unit := do
let type := mkSort (mkLevelSucc levelZero)
let typeName ← getTypeName n `Token
let tokenType := mkConst typeName
let cs := g.tokens.toList.map λ (n, _) =>
  Constructor.mk (typeName ++ n) tokenType
let d := InductiveType.mk typeName type cs
Lean.Meta.addInductive [] 0 [d]
declLexemeOf n g
-- #check mkArrow

def declSyntaxTree (n : Name) (g : Grammar) : MetaM Unit := do
let type := mkSort (mkLevelSucc levelZero)
let ns ← g.rules.mapM λ (n', _) => getTypeName n n'
let mkRuleTokenArrow : RuleToken' Name Nat → Expr → MetaM Expr
  | RuleToken'.var v, t => do
    mkArrow (mkConst ns[v]) t
  | RuleToken'.tok v, t => do
    let n := mkConst (← getTypeName n (`Token ++ v))
    let t' ← mkAppM ``_root_.Token #[n]
    mkArrow t' t
let ts ← g.rules.toList.enum.mapM λ (i, n', rs) => do
  let cs ← rs.toList.enum.mapM λ (j, p) => do
    let n := ns[i]
    let t := mkConst n
    let li := mkConst ``LineInfo
    let t ← mkArrow li (← p.foldrM mkRuleTokenArrow (← mkArrow li t))
    return Constructor.mk (n ++ `rule |>.appendIndexAfter j) t
  let n ← getTypeName n n'
  return InductiveType.mk n type cs
-- addDecl <| Declaration.inductDecl [] 0 ts false
Lean.Meta.addInductive [] 0 ts

open Lean Meta

@[commandElab grammarCmd]
def elabGrammar : CommandElab
| `(grammar $id $rules end $id') => do
  unless id == id' do
    throwError "grammar / end identifier mismatch: {id} / {id'}"
  let mut rs := #[]
  for r in rules[0].getArgs do
    let hd := r[0].getId
    let prod := r[2]
    -- println!"prod: {prod}"
    let mut prod' := #[]
    for p in prod.getArgs do
      let p := p[0]
      -- println!"p: {p}"
      let t ←
        if p.getKind == `strLit then
          -- println!"strLit: {p}"
          pure <| RuleToken'.tok <| decodeStrLit p[0].getAtomVal! |>.get!
        else if p.getKind == `ident then
          -- println!"id: {p}"
          pure <| RuleToken'.var p.getId
        else
          throwUnsupportedSyntax
      prod' := prod'.push t
    rs := rs.push <| Rule'.mk hd prod'
  let g := mkGrammar rs
  -- println!"A"
  liftTermElabM none <| declTokenType id.getId g
  -- println!"A"
  liftTermElabM none <| declSyntaxTree id.getId g
  -- println!"B"
| _ => throwUnsupportedSyntax

-- #check mkInductiveDeclEs

end Lean.Command

grammar fooBar

  foo ::= "(" foo ")" fooOrNothing
  foo ::= "."
  fooOrNothing ::=
  fooOrNothing ::= foo
  --   ^
  -- expected 'end'

end fooBar
-- #check fooBar.instIsToken
-- #print fooBar.instIsToken

instance : Inhabited (ParserM α) :=
⟨ failure ⟩
open Nat
mutual

  def parseFoo : Nat → ParserM fooBar.foo
  | 0 => failure
  | succ n =>
    (do let li ← getLineInfo
        let t ← readThisToken _
        let foo ← parseFoo n
        let t' ← readThisToken _
        let li' ← getLineInfo
        let optFoo ← parseFooOrNothing n
        return fooBar.foo.rule_0 li t foo t' optFoo li' ) <|>
    (do let li ← getLineInfo
        let t ← readThisToken _
        let li' ← getLineInfo
        return fooBar.foo.rule_1 li t li' )
  def parseFooOrNothing : Nat → ParserM fooBar.fooOrNothing
  | 0 => failure
  | succ n =>
    (do let li ← getLineInfo
        let t ← parseFoo n
        let li' ← getLineInfo
        return fooBar.fooOrNothing.rule_1 li t li' ) <|>
    (do let li ← getLineInfo
        return fooBar.fooOrNothing.rule_0 li li)

end

mutual

  def countDotFoo (x : fooBar.foo) : Nat :=
  match x with
  | x@(fooBar.foo.rule_0 li t foo t' optFoo li') =>
    have : sizeOf foo < sizeOf x := sorry
    have : sizeOf optFoo < sizeOf x := sorry
    countDotFoo foo + countDotFooOrNothing optFoo
  | fooBar.foo.rule_1 li t li' => 1

  def countDotFooOrNothing (x : fooBar.fooOrNothing) : Nat :=
  match x with
  | fooBar.fooOrNothing.rule_0 li li' => 0
  | x@(fooBar.fooOrNothing.rule_1 li foo li') =>
    have : sizeOf foo < sizeOf x := sorry
    countDotFoo foo

end
termination_by
  countDotFoo t => sizeOf t
  countDotFooOrNothing t => sizeOf t
decreasing_by assumption


mutual

  def foldCountDotFoo (acc : Nat) (x : fooBar.foo) : Nat :=
  match x with
  | x@(fooBar.foo.rule_0 li t foo t' optFoo li') =>
    have : sizeOf foo < sizeOf x := sorry
    have : sizeOf optFoo < sizeOf x := sorry
    foldCountDotFooOrNothing
      (foldCountDotFoo acc foo) optFoo
  | fooBar.foo.rule_1 li t li' => acc + 1

  def foldCountDotFooOrNothing (acc : Nat) (x : fooBar.fooOrNothing) : Nat :=
  match x with
  | fooBar.fooOrNothing.rule_0 li li' => acc
  | x@(fooBar.fooOrNothing.rule_1 li foo li') =>
    have : sizeOf foo < sizeOf x := sorry
    foldCountDotFoo acc foo

end
termination_by
  foldCountDotFoo t => sizeOf t
  foldCountDotFooOrNothing t => sizeOf t
decreasing_by assumption

mutual

  def foldCountDotFoo' (acc : Nat) (x : fooBar.foo) : Nat :=
  match x with
  | x@(fooBar.foo.rule_0 li t foo t' optFoo li') =>
    have : sizeOf foo < sizeOf x := sorry
    have : sizeOf optFoo < sizeOf x := sorry
    foldCountDotFoo' (foldCountDotFooOrNothing' acc optFoo) foo
  | fooBar.foo.rule_1 li t li' => acc + 1

  def foldCountDotFooOrNothing' (acc : Nat) (x : fooBar.fooOrNothing) : Nat :=
  match x with
  | fooBar.fooOrNothing.rule_0 li li' => acc
  | x@(fooBar.fooOrNothing.rule_1 li foo li') =>
    have : sizeOf foo < sizeOf x := sorry
    foldCountDotFoo' acc foo

end
termination_by
  foldCountDotFoo' t => sizeOf t
  foldCountDotFooOrNothing' t => sizeOf t
decreasing_by assumption

@[simp]
theorem map_failure (f : α → β) : f <$> failure = failure (f := ParserM) :=
sorry

-- TODO: adjust precedence of <|> / =
@[simp]
theorem map_orElse (f : α → β) (x y : ParserM α) :
  f <$> (x <|> y) = ((f <$> x) <|> (f <$> y)) :=
sorry

@[simp]
theorem getLineInfo_bind (x : ParserM α) :
  (getLineInfo >>= λ _ => x) = x := sorry

instance : LawfulMonad ParserM := sorry

theorem move_to_bind (f : α → β) (x : ParserM α) {g : β → ParserM γ} :
  (x >>= λ i => g (f i)) = (f <$> x) >>= g := sorry

theorem move_to_bind' {g : Nat → ParserM γ} :
  (parseFoo n >>= λ i => g (countDotFoo i)) =
  (countDotFoo <$> parseFoo n) >>= g := sorry

theorem move_to_bind'' {g : fooBar.foo → ParserM γ} (g' : Nat → ParserM γ)
        (h : ∀ t, g t = g' (countDotFoo t)) :
  (parseFoo n >>= g) = (countDotFoo <$> parseFoo n) >>= g' := sorry

theorem move_to_bind''' (x : ParserM α) (f : α → β) {g : α → ParserM γ} (g' : β → ParserM γ)
        (h : ∀ t, g t = g' (f t)) :
  (x >>= g) = (f <$> x) >>= g' := sorry

theorem move_to_bind'''' (x : ParserM α) (f : α → β) {g : α → ParserM γ} (g' : β → ParserM γ)
        (h : g = (λ t => g' (f t))) :
  (x >>= g) = (f <$> x) >>= g' := sorry

/-

stuck:

let x ← parseFoo
let x' ← parseFoo
return (countDotFoo x + countDotFoo x')

how do you move countDotFoo closer to parseFoo?

-/
open Lean.Parser.Tactic.Conv
syntax (name := convCase) "case " (ident <|> "_") (ident <|> "_")* " => " convSeq : conv

open Lean.Parser.Tactic
open Lean.Elab.Tactic Lean.Meta
open Lean.Elab.Tactic.Conv
-- #check Lean.Parser.Tactic.case
-- #fullname case
-- #fullname Tactic
-- #fullname «findTag?»
-- set_option trace.importPrivate true
-- import_private find
-- #find prefix
import_private Lean.Elab.Tactic.findTag?
-- import_private Lean.Meta.getMVarTag
-- import_private Lean.Meta.setMVarTag
-- #exit
-- #fullname evalConvSeq

@[tactic convCase]
def convCase' : Tactic
  | stx@`(conv| case $tag $hs* =>%$arr $tac:convSeq) => do
    let gs ← getUnsolvedGoals
    let g ←
      if tag.isIdent then
        let tag := tag.getId
        let some g ← findTag? gs tag | throwError "tag not found"
        pure g
      else
        getMainGoal
    let gs := gs.erase g
    let g ← renameInaccessibles g hs
    setGoals [g]
    let savedTag ← getMVarTag g
    setMVarTag g Name.anonymous
    try
      withCaseRef arr tac do
        closeUsingOrAdmit (withTacticInfoContext stx (evalConvSeq tac))
    finally
      setMVarTag g savedTag
    done
    setGoals gs
  | _ => throwUnsupportedSyntax


-- set_option pp.notation false
theorem fob (f g : Nat → ParserM Nat) :
  countDotFoo <$> parseFoo n = f n ∧
  countDotFooOrNothing <$> parseFooOrNothing n = g n
    := by
induction n
next =>
  simp [parseFoo, parseFooOrNothing]
  admit
next a ih => cases ih with | intro ih₀ ih₁ =>
constructor
next =>
  simp [parseFoo]
  simp [map_eq_pure_bind, bind_assoc]
  simp [countDotFoo]
  -- rw [move_to_bind''' (parseFoo a) countDotFoo ?x ?y]
  -- case y =>
    -- intro t
    -- generalize countDotFoo t = z; rfl
  conv =>
    lhs
    arg 1
    arg 2; intro x
    rw [move_to_bind''' (parseFoo a) countDotFoo ?x ?y]
    -- tactic => case y =>
    -- case y => intro t; generalize (countDotFoo t) = z
    case y => tactic =>
      intro t; generalize (countDotFoo t) = z; rfl
    rw [ih₀]
    arg 2; intro x
    arg 2; intro x
    rw [move_to_bind''' (parseFooOrNothing a) countDotFooOrNothing ?xx ?yy]
    case yy => tactic =>
      intro t; generalize (countDotFooOrNothing t) = z; rfl
    rw [ih₁]
    skip
    -- skip
      -- rfl
    -- skip
    -- skip
  -- rw [move_to_bind''' (parseFooOrNothing a) countDotFooOrNothing _ ?y']
  skip

    -- intro
  -- rw [move_to_bind countDotFoo (parseFoo a)]
  admit
-- next => skip

-- #check Lean.Parser.Tactic.Conv.change

-- #exit
-- #print foldCountDotFooOrNothing
-- #print foldCountDotFoo._unary._mutual
theorem fob' (f g : Nat → Nat → ParserM Nat) :
  foldCountDotFoo acc <$> parseFoo n = f acc n ∧
  foldCountDotFooOrNothing acc <$> parseFooOrNothing n = g acc n := by
induction n generalizing acc
next =>
  simp [parseFoo, parseFooOrNothing]
  admit
next a ih =>
have ih₀ := λ acc => @ih acc |>.1
have ih₁ := λ acc => @ih acc |>.2
clear ih
constructor
next =>
  simp [parseFoo]
  simp [map_eq_pure_bind, bind_assoc]
  simp [foldCountDotFoo]
  -- rw [move_to_bind''' (parseFoo a) countDotFoo ?x ?y]
  -- case y =>
    -- intro t
    -- generalize countDotFoo t = z; rfl
  conv =>
    lhs
    arg 1
    arg 2; intro x
    rw [move_to_bind''' (parseFoo a) (foldCountDotFoo _) ?x ?y]
    -- tactic => case y =>
    -- case y => intro t; generalize (countDotFoo t) = z
    case y => tactic =>
      intro t; generalize (foldCountDotFoo _ t) = z; rfl
    rw [ih₀]
    arg 2; intro x
    arg 2; intro x
    rw [move_to_bind''' (parseFooOrNothing a) (foldCountDotFooOrNothing _) ?xx ?yy]
    case yy => tactic =>
      intro t; generalize (foldCountDotFooOrNothing _ t) = z; rfl
    rw [ih₁]
    rw [bind_pure]
    -- skip
    -- skip
      -- rfl
    -- skip
    -- skip
  -- rw [move_to_bind''' (parseFooOrNothing a) countDotFooOrNothing _ ?y']
  skip

    -- intro
  -- rw [move_to_bind countDotFoo (parseFoo a)]
  admit

theorem fob'' (f g : Nat → Nat → ParserM Nat) :
  foldCountDotFoo' acc <$> parseFoo n = f acc n ∧
  foldCountDotFooOrNothing' acc <$> parseFooOrNothing n = g acc n := by
induction n generalizing acc
next =>
  simp [parseFoo, parseFooOrNothing]
  admit
next a ih =>
have ih₀ := λ acc => @ih acc |>.1
have ih₁ := λ acc => @ih acc |>.2
clear ih
constructor
next =>
  simp [parseFoo]
  simp [map_eq_pure_bind, bind_assoc]
  simp [foldCountDotFoo']
  conv =>
    lhs
    arg 1
    arg 2; intro x
    rw [move_to_bind''' (parseFoo a) (foldCountDotFoo' _) ?x ?y]
    case y => tactic =>
      -- this can't work because we're propagating information from
      -- later parse trees to earlier parse trees
      intro t; generalize (foldCountDotFoo' _ t) = z; rfl
    rw [ih₀]
    arg 2; intro x
    arg 2; intro x
    rw [move_to_bind''' (parseFooOrNothing a) (foldCountDotFooOrNothing _) ?xx ?yy]
    case yy => tactic =>
      intro t; generalize (foldCountDotFooOrNothing _ t) = z; rfl
    rw [ih₁]
    rw [bind_pure]
    -- skip
    -- skip
      -- rfl
    -- skip
    -- skip
  -- rw [move_to_bind''' (parseFooOrNothing a) countDotFooOrNothing _ ?y']
  skip
    -- intro
  -- rw [move_to_bind countDotFoo (parseFoo a)]
  admit

-- next =>
--   simp [parseFoo]
--   admit
-- next a ih =>
--   simp [parseFoo]
--   simp [map_eq_pure_bind, bind_assoc]
--   simp [countDotFoo]
--   rw [move_to_bind countDotFoo (parseFoo a)]
--   admit

-- #print fooBar.Token
-- #print fooBar.lexemeOf
-- #print fooBar.foo
-- #print fooBar.fooOrNothing
-- invalid 'end', insufficient scopes
