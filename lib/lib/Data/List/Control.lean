
namespace List

variable {m} [Monad m]

def zipWithM : List α → List β → (α → β → m γ) → m (List γ)
| [], _, f => pure []
| _, [], f => pure []
| x :: xs, y :: ys, f => do
  let z ← f x y
  return z :: (← zipWithM xs ys f)

end List
