import Lib.Tactic
import Lean.Meta.Basic

initialize functorSimpAttr : Lean.Meta.SimpExtension ←
  Lean.Meta.registerSimpAttr `functor
      "simp attribute for functor equations"
