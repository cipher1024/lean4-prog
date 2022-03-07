
import Lib.Meta.DeclGraph

namespace Std
open Lean
class ToFormatM (m : Type → Type v) (α : Type u) where
  formatM : α → m Format
  modifier : List Name := []

open ToFormatM

instance [Monad m] [ToFormatM m α] : ToFormatM m (List α) where
  formatM x := do return format (← x.mapM formatM)

instance [Monad m] [ToFormatM m α] : ToFormatM m (Subarray α) where
  formatM x := do return format (← x.toArray.mapM formatM)

instance [Monad m] [ToFormatM m α] : ToFormatM m (Array α) where
  formatM x := do return format (← x.mapM formatM)

instance [MonadLiftT m n] [ToFormatM m α] : ToFormatM n α where
  formatM x := liftM (formatM x : m _)
  modifier := ToFormatM.modifier m α

instance [MonadLiftT n m] [Monad m] [ToFormatM m α] : ToFormatM m (n α) where
  formatM x := do
    let x : α ← (x : m α)
    liftM (formatM x : m _)
  modifier := ToFormatM.modifier m α

instance (priority := low)
         [Pure m] [ToFormat α] : ToFormatM m α where
  formatM x := pure <| format x

end Std

namespace Lean
open Std ToFormatM Meta
open Lean.Elab.Tactic

instance : ToFormatM MetaM Expr where
  formatM := Meta.ppExpr

instance : ToFormatM MetaM FVarId where
  formatM v := Meta.ppExpr <| mkFVar v

def AsConst := Name
@[inline] def asConst : Name → AsConst := id

def WithType := Expr
@[inline] def withType : Expr → WithType := id

def TypeOf := Expr
@[inline] def typeOf : Expr → TypeOf := id

def AsGoal := MVarId
@[inline] def asGoal : MVarId → AsGoal := id

def MainGoal := Unit
@[inline] def mainGoal : MainGoal := ()

def GoalList := Unit
@[inline] def goalList : GoalList := ()

instance : ToFormatM MetaM AsConst where
  formatM x := do
    let c ← mkConstWithLevelParams x
    let t ← Meta.ppExpr (← Meta.inferType c)
    let x ← Meta.ppExpr c
    return x ++ " : " ++ t
  modifier := [`asConst]

instance : ToFormatM MetaM WithType where
  formatM x := do
    let t ← Meta.ppExpr (← Meta.inferType x)
    let x ← Meta.ppExpr x
    return x ++ " : " ++ t
  modifier := [`withType]

instance : ToFormatM MetaM TypeOf where
  formatM x := do
    let t ← Meta.ppExpr (← Meta.inferType x)
    return t
  modifier := [`typeOf]

instance : ToFormatM MetaM AsGoal where
  formatM x := Format.indentD <$> Meta.ppGoal x
  modifier := [`asGoal]

instance : ToFormatM TacticM MainGoal where
  formatM x := do
    let g ← getMainGoal
    Format.indentD <$> liftMetaM (Meta.ppGoal g)

instance : ToFormatM TacticM GoalList where
  formatM x := do
    let gs ← getGoals
    let mut gs ← gs.mapM λ g =>
       liftMetaM (Meta.ppGoal g)
    if gs.length = 0 then
      gs := ["No goals"]
    else if gs.length > 1 then
      gs := s!"{gs.length} Goals" :: gs
    return Format.joinSep (gs.map Format.indentD) Format.line

instance [ToFormatM MetaM α] [MonadLiftT MetaM m] : ToFormatM m α where
  formatM x := Meta.liftMetaM <| formatM x

end Lean
