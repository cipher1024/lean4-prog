import Lean.Elab.Tactic
-- import Lean.Elab.Tactic.Simp

#exit

#check Lean.Meta.getSimpLemmas
#check Lean.Elab.Tactic.mkSimpContext
#check Lean.Elab.Tactic.evalSimp

theorem pointfree_left {f : α → β} {g : β → γ} :
  g (f x) = y →
  (g ∘ f) x = y := id

theorem pointfree_right {f : α → β} {g : β → γ} :
  x = g (f y) →
  x = (g ∘ f) y := id

theorem finish_pointfree {f g : α → β} :
  (∀ x, f x = g x) → f = g := funext

namespace Lean.Meta

namespace MakeBuddies



end MakeBuddies

open Lean.Expr
open Meta
open Lean.Macro
open Lean.Meta

-- def mkLam (v : Expr) (b : Expr) : MetaM Expr := do
-- let lctx ← getLCtx
-- let decl := lctx.get! v.fvarId!
-- let n :=  decl.userName
-- let t :=  decl.type
-- let bi :=  decl.binderInfo
-- return mkLambda n bi t (b.abstract #[v])
-- open Lean.Meta (mkLambdaFVars)

partial def finishPointFree (pr : Expr) : MetaM (FVarId × Expr) := do
match (← inferType pr) with
| app (app eq (app f x@(fvar x' _) _) _) (app f' y@(fvar y' _) _) _ => do
  unless (x' == y') do
    throwError "cannot transform into point-free: {x} {y}";
  let args := #[none, none, f, f', (← mkLambdaFVars #[x] pr)]
  let l ← mkAppOptM ``finish_pointfree args
  return (x', l)
| t => do
  throwError "bad shape {(← ppExpr t)}"

-- #check @pointfree_right

partial def mkPointFreeRight (pr : Expr) : MetaM (FVarId × Expr) := do
match (← inferType pr) with
| app (app eq lhs _) (app f (app g x _) _) _ =>
      let args := #[none, none, none, none, x, g, f, pr]
      (mkAppOptM ``pointfree_right args
       >>= mkPointFreeRight)
| _ => finishPointFree pr


partial def mkPointFreeLeft (pr : Expr) : MetaM (FVarId × Expr) := do
match (← inferType pr) with
| app (app eq (app f (app g x _) _) _) _ _ =>
      let args := #[none, none, none, x, none, g, f, pr]
      (mkAppOptM ``pointfree_left args
       >>= mkPointFreeLeft)
| _ => mkPointFreeRight pr



def makeBuddies (n : Name) : MetaM (Name × Name) := do
let info ← getConstInfo n
let ls : List Name := info.levelParams
let l ← mkConst n (ls.map mkLevelParam)
let n' := Name.appendAfter info.name "_pointfree"
let t ← inferType l
forallTelescopeReducing t λ args hd => do
  for x in args do
    IO.println s!"{(← ppExpr x)} : {(← ppExpr (← inferType x))}"
  IO.println s!"{(← ppExpr hd)}"
  let l' := mkAppN l args
  IO.println s!"{(← ppExpr l')}"
  IO.println s!"{(← ppExpr (← inferType l'))}"
  let (v, e) ← mkPointFreeLeft l'
  let args := args.erase (mkFVar v)
  let e ← mkLambdaFVars args e
  let t ← inferType e
  -- let t ← mkForallFVars args (← inferType e)
  modifyEnv λ env => env.add
    <| ConstantInfo.thmInfo
    <| { name := n',
         levelParams := ls,
         type := t,
         value := e }
  IO.println s!"{(← ppExpr e)} : {(← ppExpr (← inferType e))}"
  return (n, n')

#eval makeBuddies ``LawfulFunctor.comp_map
#check @LawfulFunctor.comp_map_pointfree
#check getSimpLemmas
namespace Buddies

private partial def isPerm : Expr → Expr → MetaM Bool
  | Expr.app f₁ a₁ _, Expr.app f₂ a₂ _ => isPerm f₁ f₂ <&&> isPerm a₁ a₂
  | Expr.mdata _ s _, t => isPerm s t
  | s, Expr.mdata _ t _ => isPerm s t
  | s@(Expr.mvar ..), t@(Expr.mvar ..) => isDefEq s t
  | Expr.forallE n₁ d₁ b₁ _, Expr.forallE n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.lam n₁ d₁ b₁ _, Expr.lam n₂ d₂ b₂ _ => isPerm d₁ d₂ <&&> withLocalDeclD n₁ d₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.letE n₁ t₁ v₁ b₁ _, Expr.letE n₂ t₂ v₂ b₂ _ =>
    isPerm t₁ t₂ <&&> isPerm v₁ v₂ <&&> withLetDecl n₁ t₁ v₁ fun x => isPerm (b₁.instantiate1 x) (b₂.instantiate1 x)
  | Expr.proj _ i₁ b₁ _, Expr.proj _ i₂ b₂ _ => i₁ == i₂ <&&> isPerm b₁ b₂
  | s, t => s == t

private def checkTypeIsProp (type : Expr) : MetaM Unit :=
  unless (← isProp type) do
    throwError "invalid 'simp', proposition expected{indentExpr type}"

private def mkSimpLemmaCore (e : Expr) (levelParams : Array Name) (proof : Expr) (post : Bool) (prio : Nat) (name? : Option Name) : MetaM SimpLemma := do
  let type ← instantiateMVars (← inferType e)
  withNewMCtxDepth do
    let (xs, _, type) ← withReducible <| forallMetaTelescopeReducing type
    let type ← whnfR type
    let (keys, perm) ←
      match type.eq? with
      | some (_, lhs, rhs) => pure (← DiscrTree.mkPath lhs, ← isPerm lhs rhs)
      | none => throwError "unexpected kind of 'simp' theorem{indentExpr type}"
    return { keys := keys, perm := perm, post := post, levelParams := levelParams, proof := proof, name? := name?, priority := prio }

private partial def shouldPreprocess (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun xs result => return !result.isEq

private partial def preprocess (e type : Expr) (inv : Bool) : MetaM (List (Expr × Expr)) := do
  let type ← whnf type
  if type.isForall then
    forallTelescopeReducing type fun xs type => do
      let e := mkAppN e xs
      let ps ← preprocess e type inv
      ps.mapM fun (e, type) =>
        return (← mkLambdaFVars xs e, ← mkForallFVars xs type)
  else if let some (_, lhs, rhs) := type.eq? then
    if inv then
      let type ← mkEq rhs lhs
      let e    ← mkEqSymm e
      return [(e, type)]
    else
      return [(e, type)]
  else if let some (lhs, rhs) := type.iff? then
    if inv then
      let type ← mkEq rhs lhs
      let e    ← mkEqSymm (← mkPropExt e)
      return [(e, type)]
    else
      let type ← mkEq lhs rhs
      let e    ← mkPropExt e
      return [(e, type)]
  else if let some (_, lhs, rhs) := type.ne? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    let type ← mkEq (← mkEq lhs rhs) (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some p := type.not? then
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'False'"
    let type ← mkEq p (mkConst ``False)
    let e    ← mkEqFalse e
    return [(e, type)]
  else if let some (type₁, type₂) := type.and? then
    let e₁ := mkProj ``And 0 e
    let e₂ := mkProj ``And 1 e
    return (← preprocess e₁ type₁ inv) ++ (← preprocess e₂ type₂ inv)
  else
    if inv then
      throwError "invalid '←' modifier in rewrite rule to 'True'"
    let type ← mkEq type (mkConst ``True)
    let e    ← mkEqTrue e
    return [(e, type)]

private def mkSimpLemmasFromConst (declName : Name) (post : Bool) (inv : Bool) (prio : Nat) : MetaM (Array SimpLemma) := do
  let cinfo ← getConstInfo declName
  let val := mkConst declName (cinfo.levelParams.map mkLevelParam)
  withReducible do
    let type ← inferType val
    checkTypeIsProp type
    if inv || (← shouldPreprocess type) then
      let mut r := #[]
      for (val, type) in (← preprocess val type inv) do
        let auxName ← mkAuxLemma cinfo.levelParams type val
        r := r.push <| (← mkSimpLemmaCore (mkConst auxName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst auxName) post prio declName)
      return r
    else
      #[← mkSimpLemmaCore (mkConst declName (cinfo.levelParams.map mkLevelParam)) #[] (mkConst declName) post prio declName]

abbrev SimpExtension := SimpleScopedEnvExtension SimpEntry SimpLemmas

def SimpExtension.getLemmas (ext : SimpExtension) : CoreM SimpLemmas :=
  return ext.getState (← getEnv)

def addSimpLemma (ext : SimpExtension) (declName : Name) (post : Bool) (inv : Bool) (attrKind : AttributeKind) (prio : Nat) : MetaM Unit := do
  let simpLemmas ← mkSimpLemmasFromConst declName post inv prio
  for simpLemma in simpLemmas do
    ext.add (SimpEntry.lemma simpLemma) attrKind

def mkSimpAttr (attrName : Name) (attrDescr : String) (ext : SimpExtension) : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    add   := fun declName stx attrKind =>
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        if (← isProp info.type) then
          let post :=
            if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
          let prio ← getAttrParamOptPrio stx[2]
          addSimpLemma ext declName post (inv := false) attrKind prio
        else if info.hasValue then
          ext.add (SimpEntry.toUnfold declName) attrKind
        else
          throwError "invalid 'simp', it is not a proposition nor a definition (to unfold)"
      discard <| go.run {} {}
    erase := fun declName => do
      let s ← ext.getState (← getEnv)
      let s ← s.erase declName
      modifyEnv fun env => ext.modifyState env fun _ => s
  }

def mkSimpExt (extName : Name) : IO SimpExtension :=
  registerSimpleScopedEnvExtension {
    name     := extName
    initial  := {}
    addEntry := fun d e =>
      match e with
      | SimpEntry.lemma e => addSimpLemmaEntry d e
      | SimpEntry.toUnfold n => d.addDeclToUnfold n
  }

def registerSimpAttr (attrName : Name) (attrDescr : String) (extName : Name := attrName.appendAfter "Ext") : IO SimpExtension := do
  let ext ← mkSimpExt extName
  mkSimpAttr attrName attrDescr ext
  return ext

builtin_initialize mySimpExtension : SimpExtension ← registerSimpAttr `my_simp "simplification theorem with buddies"

def getSimpLemmas : CoreM SimpLemmas :=
  simpExtension.getLemmas

end Buddies

end Lean.Meta

namespace Lean.Elab.Tactic
-- abbrev mkDischargeWrapper :=
-- _root_.Lean.Elab.Tactic.mkDischargeWrapper

open Lean.Meta


private def addDeclToUnfoldOrLemma (lemmas : Meta.SimpLemmas) (e : Expr) (post : Bool) (inv : Bool) : MetaM Meta.SimpLemmas := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← isProp info.type) then
      lemmas.addConst declName (post := post) (inv := inv)
    else
      if inv then
        throwError "invalid '←' modifier, '{declName}' is a declaration name to be unfolded"
      lemmas.addDeclToUnfold declName
  else
    lemmas.add #[] e (post := post) (inv := inv)

private def addSimpLemma (lemmas : Meta.SimpLemmas) (stx : Syntax) (post : Bool) (inv : Bool) : TermElabM Meta.SimpLemmas := do
  let (levelParams, proof) ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return (r.paramNames, r.expr)
    else
      return (#[], e)
  lemmas.add levelParams proof (post := post) (inv := inv)

/--
  Elaborate extra simp lemmas provided to `simp`. `stx` is of the `simpLemma,*`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased lemmas (`- id`),
  this option only makes sense for `simp_all`.
-/
private def elabSimpArgs (stx : Syntax) (ctx : Simp.Context) (eraseLocal : Bool) : TacticM ElabSimpArgsResult := do
  if stx.isNone then
    return { ctx }
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? term

    syntax simpErase := "-" ident
    -/
    withMainContext do
      let mut lemmas  := ctx.simpLemmas
      let mut starArg := false
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpErase then
          if eraseLocal && (← Term.isLocalIdent? arg[1]).isSome then
            -- We use `eraseCore` because the simp lemma for the hypothesis was not added yet
            lemmas ← lemmas.eraseCore arg[1].getId
          else
            let declName ← resolveGlobalConstNoOverloadWithInfo arg[1]
            lemmas ← lemmas.erase declName
        else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          let inv  := !arg[1].isNone
          let term := arg[2]
          match (← resolveSimpIdLemma? term) with
          | some e => lemmas ← addDeclToUnfoldOrLemma lemmas e post inv
          | _      => lemmas ← addSimpLemma lemmas term post inv
        else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
          starArg := true
        else
          throwUnsupportedSyntax
      return { ctx := { ctx with simpLemmas := lemmas }, starArg }
where
  resolveSimpIdLemma? (simpArgTerm : Syntax) : TacticM (Option Expr) := do
    if simpArgTerm.isIdent then
      try
        Term.resolveId? simpArgTerm (withInfo := true)
      catch _ =>
        return none
    else
      Term.elabCDotFunctionAlias? simpArgTerm

private def mkDischargeWrapper (optDischargeSyntax : Syntax) : TacticM Simp.DischargeWrapper := do
  if optDischargeSyntax.isNone then
    return Simp.DischargeWrapper.default
  else
    let (ref, d) ← tacticToDischarge optDischargeSyntax[0][3]
    return Simp.DischargeWrapper.custom ref d

-- TODO: move?
private def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

/--
  If `ctx == false`, the config argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise.
  If `ctx == false`, the `discharge` option must be none -/
def mkSimpContext' (stx : Syntax) (eraseLocal : Bool) (ctx := false) (ignoreStarArg : Bool := false) : TacticM MkSimpContextResult := do
  if ctx && !stx[2].isNone then
    throwError "'simp_all' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[3].isNone
  let simpLemmas ←
    if simpOnly then
      ({} : SimpLemmas).addConst ``eq_self
    else
      getSimpLemmas
  let congrLemmas ← getCongrLemmas
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) {
    config      := (← elabSimpConfig stx[1] (ctx := ctx))
    simpLemmas, congrLemmas
  }
  if !r.starArg || ignoreStarArg then
    return { r with fvarIdToLemmaId := {}, dischargeWrapper }
  else
    let ctx := r.ctx
    let erased := ctx.simpLemmas.erased
    let hs ← getPropHyps
    let mut ctx := ctx
    let mut fvarIdToLemmaId := {}
    for h in hs do
      let localDecl ← getLocalDecl h
      unless erased.contains localDecl.userName do
        let fvarId := localDecl.fvarId
        let proof  := localDecl.toExpr
        let id     ← mkFreshUserName `h
        fvarIdToLemmaId := fvarIdToLemmaId.insert fvarId id
        let simpLemmas ← ctx.simpLemmas.add #[] proof (name? := id)
        ctx := { ctx with simpLemmas }
    return { ctx, fvarIdToLemmaId, dischargeWrapper }

@[tactic Lean.Parser.Tactic.simp] def evalSimp' : Tactic := fun stx => do
  IO.println "simp!!!"
  -- let { ctx, fvarIdToLemmaId, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  -- -- trace[Meta.debug] "Lemmas {← toMessageData ctx.simpLemmas.post}"
  -- dischargeWrapper.with fun discharge? =>
  --   simpLocation ctx discharge? fvarIdToLemmaId (expandOptLocation stx[5])

end Lean.Elab.Tactic

example : True := by simp
