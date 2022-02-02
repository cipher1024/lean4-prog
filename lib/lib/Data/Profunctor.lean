
import Lib.Data.Prod.Defs

class Profunctor (p : Type u → Type v → Type w) where
  dimap {α α' β β'} :
    (α' → α) →
    (β → β') →
    p α β → p α' β'

namespace Profunctor

variable {p} [Profunctor.{u,v,w} p]
variable {α α' : Type u} {β β' : Type v}
variable (f : α' → α) (g : β → β')

def lmap : p α β → p α' β := dimap f id

def rmap : p α β → p α β' := dimap id g

end Profunctor

open Profunctor

class LawfulProfunctor (p) [Profunctor p] where
  dimap_id {α β} (x : p α β) : dimap id id x = x
  dimap_comp {α α' β β' γ γ'}
             (f : α → β) (g : β → γ)
             (f' : α' → β') (g' : β' → γ') (x : p _ _) :
    dimap f g' (dimap g f' x) =
    dimap (g ∘ f) (g' ∘ f') x

instance : Profunctor (.→ .) where
  dimap f g x := g ∘ x ∘ f

instance : LawfulProfunctor (.→ .) where
  dimap_id x := rfl
  dimap_comp f g f' g' x := rfl

-- class StrongProfunctor (p) [Profunctor.{u,u,u} p] where
--   first {α β γ : Type u} :
--     p α β → p (α × γ) (β × γ)

-- namespace StrongProfunctor
-- open Profunctor
-- variable {p} [Profunctor.{u,u} p] [StrongProfunctor p]
-- variable {α β γ : Type u}

-- def second (x : p β γ) : p (α × β) (α × γ) :=
-- dimap Prod.swap Prod.swap (first (γ := α) x)

-- end StrongProfunctor

-- open Prod StrongProfunctor
-- set_option pp.explicit true
-- set_option pp.universes true
-- class LawfulStrongProfunctor (p) [Profunctor p] [StrongProfunctor.{u} p] where
--   lmap_fst {α β γ γ' : Type u} :
--     lmap (β := γ × γ') (p := p) (@fst α β) = rmap (p := p) fst ∘ _
