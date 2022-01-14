
import Lib.Data.Foldable
import Lib.Data.List.Instances

class MonoFoldable (F : Type u) (α : outParam (Type v)) where
  foldl (f : β → α → β) (x₀ : β) (t : F) : β
  foldr (f : α → β → β) (x₀ : β) (t : F) : β
  toList (x : F) : List α := foldl (flip (.::.)) [] x |>.reverse
  toArray (x : F) : Array α := toList x |>.toArray
  length (x : F) : Nat :=
    ULift.down <| foldl (λ n _ => ⟨n.1.succ⟩) ⟨0⟩ x

instance {F} [Foldable F] : MonoFoldable (F α) α where
  foldl := Foldable.foldl
  foldr := Foldable.foldr
  toList := Foldable.toList
  toArray := Foldable.toArray
  length := Foldable.length

namespace MonoFoldable

variable {F} [MonoFoldable F α]

def foldMap [One m] [Mul m] (f : α → m) (x : F) : m :=
MonoFoldable.foldl (λ acc x => f x * acc) One.one x


end MonoFoldable

open MonoFoldable

class LawfulMonoFoldable (F : Type u) (α : outParam (Type v))
      [outParam (MonoFoldable F α)] where
  foldl_sim {β γ : Type v} {f : β → α → β} {g : γ → α → γ} {SIM : β → γ → Prop} {x₀ y₀} (t : F) :
    SIM x₀ y₀ →
    (∀ a x y, SIM x y → SIM (f x a) (g y a)) →
    SIM (foldl f x₀ t) (foldl g y₀ t)
  foldr_eq_foldMap {β} (f : α → β → β) (x : F) (x₀ : β) :
    foldr f x₀ x =
    (foldMap (λ x => Op.mk $ Endo.mk (f x)) x).run.run x₀
  toArray_toList (x : F) : (toList x).toArray = toArray x
    -- by apply Reflexive.refl
  length_toList (x : F) : (toList x).length = length x
 -- :=
 --    -- let H := @foldl_sim
 --    -- by prove_length_toList H α x
 --       have H' : ∀ xs n, List.length xs = n → List.length xs.reverse = n := sorry
 --       suffices H : ((foldl (flip (.::.)) [] x).length =
 --                 ULift.down (foldl (β := ULift Nat)
 --                            (λ ⟨n⟩ _ => ⟨n.succ⟩) ⟨0⟩ x))
 --                by apply H' _ _ H
 --       let R :=
 --         λ (x : List α) (y : ULift Nat) => x.length = y.down;
 --       by apply foldl_sim (SIM := R)
 --          . apply Reflexive.refl
 --          . simp [flip]; auto
  foldl_toList {β} (f : β → α → β) (x₀ : β) (x : F) :
    (toList x).foldl f x₀ = foldl f x₀ x
 -- :=
 --    -- let H := @foldl_sim
 --    -- by prove_foldl_toList H
 --       suffices H : ((foldl (flip (.::.)) [] x).reverse.foldl f x₀ =
 --                 foldl f x₀ x)
 --                by {trans <;> try assumption}
 --       let R :=
 --         λ (l : List α) (y : β) => l.reverse.foldl f x₀ = y;
 --       by
 --          apply foldl_sim (SIM := R) x
 --       -- apply sim (SIM := R)
 --          . apply Reflexive.refl
 --          focus simp [flip]

instance {F} [Foldable F] [LawfulFoldable F] :
         LawfulMonoFoldable (F α) α where
  foldl_sim := LawfulFoldable.foldl_sim
  foldr_eq_foldMap := LawfulFoldable.foldr_eq_foldMap
  toArray_toList := LawfulFoldable.toArray_toList
  length_toList := LawfulFoldable.length_toList
  foldl_toList := LawfulFoldable.foldl_toList
