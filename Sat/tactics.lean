
macro "obtain " p:term " from " d:term : tactic =>
  `(tactic| match $d:term with | $p:term => ?_)

macro "left" : tactic =>
  `(tactic| apply Or.inl)

macro "right" : tactic =>
  `(tactic| apply Or.inr)

macro "refl" : tactic =>
  `(tactic| apply rfl)

macro "exfalso" : tactic =>
  `(tactic| apply False.elim)

macro "byContradiction" h: ident : tactic =>
  `(tactic| apply Classical.byContradiction; intro h)

-- theorem swapHyp {p q : Prop} (h : p) (h' : ¬ p) : q := by
--   cases h' h

-- macro "swapHyp" h:term "as" h':ident : tactic =>
--   `(tactic| apply Classical.byContradiction; intro $h' <;>
--             first
--             | apply $h ; clear $h
--             | apply swapHyp $h <;> clear $h
--               )
