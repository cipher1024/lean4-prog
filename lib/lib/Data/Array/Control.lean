namespace Array

section Control

variable {m : Type u → Type v} [Monad m] [Alternative m]
variable {α : Type w} {β : Type u} (f : α → m β)

@[inline]
unsafe def firstMUnsafe (as : Array α) (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] firstM (i : USize) (stop : USize) : m β := do
    if i == stop then
      failure
    else
      f (as.uget i lcProof) <|>
      firstM (i+1) stop
  if start < stop then
    if stop ≤ as.size then
      firstM (USize.ofNat start) (USize.ofNat stop)
    else
      failure
  else
    failure

@[implementedBy firstMUnsafe]
def firstM (as : Array α) (start := 0) (stop := as.size) : m β :=
  let first (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => failure
        | i'+1 =>
          f (as.get ⟨j, Nat.lt_of_lt_of_le hlt h⟩) <|>
          loop i' (j+1)
      else
        failure
    loop (stop - start) start
  if h : stop ≤ as.size then
    first stop h
  else
    first as.size (Nat.le_refl _)

end Control

def mapMaybe (f : α → Option β) : Array α → Array β :=
Array.foldl
  (λ acc a =>
    match f a with
    | none => acc
    | some a => acc.push a )
  #[]

end Array
