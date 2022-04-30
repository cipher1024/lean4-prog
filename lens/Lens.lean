
import Lib.Tactic
import Lib.Meta

import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

structure Lens (s a : Type _) where
  get : s → a
  modify : (a → a) → s → s

namespace Lens

attribute [inline] Lens.modify

@[inline]
def set (ln : Lens s a) (v : a) (x : s) : s :=
ln.modify (λ _ => v) x

@[inline]
def comp : Lens s a → Lens a a' → Lens s a'
| ⟨get₀,f₀⟩, ⟨get₁,f₁⟩ =>
  ⟨λ x => get₁ (get₀ x), λ f x => f₀ (f₁ f) x ⟩
  -- get := ln₁.get ∘ ln₀.get
  -- modify := ln₀.modify ∘ ln₁.modify

scoped notation x " & " ln " %~ " f => Lens.modify ln f x
scoped notation x " & " ln " .~ " v => Lens.set ln v x
scoped notation x "^." ln => Lens.get ln x
scoped infix:50 "/." => comp

end Lens

-- This is the target of the derive handler
def Lenses := Unit

namespace Lean.Meta


open Lean.Elab
open Lean.Elab.Term
open Lean.Elab.Tactic

def mkLens (pre struct field : Name) : TermElabM Name :=
let n := struct ++ pre ++ field
withDeclName n do
withFieldType struct field λ vs t => do
withFreshMacroScope do
    let v::vs := vs
      | throwError "badly formed field type"
    let info ← getFieldInfo! struct field
  -- withLCtx lctx {} do
    let t ← instantiateMVars t
    let s ← inferType (← instantiateMVars v)
    -- let s ← inferType v
    let lensT ← mkAppOptM ``Lens #[s, t]
    let vs := vs.reverse.toArray
    let prj ← mkAppOptM info.projFn <| vs.map some

    let setterT ← mkArrow (← mkArrow t t) (← mkArrow s s)
    let instInhabited ← mkAppOptM ``Inhabited #[t]
    let inst ← optional (synthInstance instInhabited)
    let delabS ← Lean.PrettyPrinter.delab s
    let setter ←
      if inst.isSome then
        `(λ f x =>
           let a := $(mkIdent info.projFn) x
           let x' : $delabS := { x with
             $(mkIdent field):ident := default }
           { x' with
             $(mkIdent field):ident :=
              f a } )
      else
        `(λ f x =>
           let a := $(mkIdent info.projFn) x
           { x with
             $(mkIdent field):ident :=
              f a } )
    let setter ← instantiateMVars
      (← Term.elabTerm setter (some setterT))
    let setter ← addDef [] (n.mkStr "modify")
      (← mkForallFVars vs setterT)
      (← mkLambdaFVars vs setter)
    setInlineAttribute setter
    -- let ppSetter ← ppExpr setter
    let mk ← mkAppOptM ``Lens.mk
      #[s, t, prj, ← mkAppOptM setter <| vs.map some]
    discard <| addDef [] n
      (← mkForallFVars vs lensT)
      (← mkLambdaFVars vs mk)
    setInlineAttribute n
    return n

def getLens (struct field : Name) : TermElabM Name := do
  let pre := `Lens
  let n := struct ++ pre ++ field
  let env ← getEnv
  if env.contains n then return n
  else mkLens pre struct field

open Lean.Elab.Command

def lensesDeriveHandler : DerivingHandlerNoArgs
| #[struct] => do
  let env ← getEnv
  let fields := getStructureFieldsFlattened env struct
  liftTermElabM none <|
    fields.forM (discard <| getLens struct .)
  return true
| _ => return false

initialize
  Lean.Elab.registerBuiltinDerivingHandler `Lenses
    lensesDeriveHandler

end Lean.Meta
