
inductive These (α β : Type _) where
  | inl (x : α)
  | inr (y : β)
  | both (x : α) (y : β)

namespace These

def map (f : α → α') (g : β → β') : These α β → These α' β'
| inl x => inl <| f x
| inr x => inr <| g x
| both x y => both (f x) (g y)

end These
