
import Lib.Logic.Classical
import Lib.Data.MonoFunctor
import Lib.Data.MonoFoldable
import Lib.Data.MonoTraversable
import Lib.Data.List.Instances
import Lib.Meta.ImportPrivate

namespace Classical

theorem contradiction (h : p) (h' : ¬ p) : q := by
auto

end Classical


-- syntax "repeat " tacticSeq : tactic
-- macro_rules
--   | `(tactic| repeat $seq) => `(tactic| first | ($seq); repeat $seq | skip)

namespace String

@[implementedBy map]
def map' (f : Char → Char) : String → String
| ⟨ data ⟩ => ⟨ Functor.map f data ⟩

instance : MonoFunctor String Char where
  map := map'

instance : LawfulMonoFunctor String Char where
  id_map := by
    intros; next x =>
    cases x; simp [MonoFunctor.map, map']
  comp_map := by
    intros; next x =>
    cases x; simp [MonoFunctor.map, map']

variable {β : Type}

@[inline]
def foldlImpl (f : β → Char → β) (x₀ : β) : String → β :=
String.foldl f x₀

@[implementedBy foldlImpl]
def foldl' (f : β → Char → β) (x₀ : β) : String → β
| ⟨ data ⟩ => Foldable.foldl f x₀ data

@[inline]
def foldrImpl (f : Char → β → β) (x₀ : β) : String → β :=
String.foldr f x₀

@[implementedBy foldrImpl]
def foldr' (f : Char → β → β) (x₀ : β) : String → β
| ⟨ data ⟩ => Foldable.foldr f x₀ data

def toArray (s : String) : Array Char :=
String.foldl' Array.push (Array.mkEmpty s.length) s

instance : MonoFoldable String Char where
  foldl := String.foldl'
  foldr := String.foldr'
  toList := String.toList
  toArray := String.toArray
  length := String.length

open MonoFoldable

instance : LawfulMonoFoldable String Char where
  foldl_sim :=
    by intros _ _ _ f SIM x₀ y₀ t a ih
       cases t; simp [foldl, MonoFoldable.foldl]
       auto [LawfulFoldable.foldl_sim]
  foldr_eq_foldMap :=
    by intros _ _ t _
       cases t; simp [foldr, MonoFoldable.foldr]
       auto [LawfulFoldable.foldr_eq_foldMap]
  toArray_toList :=
    by intros t
       cases t with | mk data =>
       simp [toList, toArray, String.foldl']
       simp [String.toList,
             String.toArray, String.foldl']
       show Foldable.toArray data = _
       rw [LawfulFoldable.toArray_eq]
       refl
  length_toList := by
    intros t; cases t; refl
  foldl_toList := by
    intros β f x₀ t; cases t; refl

section mapM

variable {M} [Monad M]
@[specialize] partial def mapMAux (f : Char → M Char) (i : Pos) (s : String) : M String :=
  if s.atEnd i then s
  else do
    let c ← f (s.get i)
    let s := s.set i c
    mapMAux f (s.next i) s

@[inline] def mapMImpl (f : Char → M Char) (s : String) : M String :=
  mapMAux f 0 s

@[implementedBy mapMImpl] def mapM (f : Char → M Char) (s : String) : M String :=
  String.mk <$> s.data.mapM f

end mapM


section mapM

variable {F} [Applicative F]

def mapA (f : Char → F Char) (s : String) : F String :=
String.mk <$> Traversable.traverse f s.data

end mapM

instance : MonoTraversable String Char where
  traverse := mapA
  mapM := mapM

open LawfulMonoTraversable
instance : LawfulMonoTraversable String Char where
  map_eq_traverse := by
    intros; next x => cases x with | mk data =>
    simp [MonoTraversable.traverse, MonoFunctor.map, map']
    simp [LawfulTraversable.map_eq_traverse]; refl
  foldl_eq_traverse := by
    intros; next x y => cases x with | mk data =>
    simp [MonoFoldable.foldl, foldl']
    simp [LawfulTraversable.foldl_eq_traverse]; refl
  traverse_eq_mapM := by
    intros; next x => cases x with | mk data =>
    simp [MonoTraversable.traverse, mapA]
    simp [LawfulTraversable.traverse_eq_mapM]; refl
  comp_traverse := by
    intros; next x y z => cases x with | mk data =>
    simp [MonoTraversable.traverse, mapA]
    simp [LawfulTraversable.comp_traverse]; refl
  traverse_sim := by
    intros; next x SIM _ _ _ => cases x with | mk data =>
    simp [MonoTraversable.traverse, mapA]
    auto [LawfulTraversable.traverse_sim, ApplicativeRel.naturality]

theorem toList_inj {s₀ s₁ : String} :
  s₀.toList = s₁.toList → s₀ = s₁ :=
by intro h; cases s₀; cases s₁; cases h; rfl

protected def utf8ByteSizeAux : List Char → Nat → Nat
  | List.nil,       r => r
  | List.cons c cs, r => String.utf8ByteSizeAux cs (r + (csize c))

theorem le_utf8ByteSizeAux xs n :
  n + List.length xs ≤ String.utf8ByteSizeAux xs n := by
induction xs generalizing n
<;> simp only [List.length, String.utf8ByteSizeAux, Nat.add_one, Nat.add_succ_eq_succ_add]
next => simp [Nat.add_zero]; refl
next ih =>
  trans _ </> try apply ih
  -- rw [Nat.add_succ_eq_succ_add]
  apply Nat.add_le_add_right
  rw [Nat.succ_eq_add_one]
  apply Nat.add_le_add_left
  simp [csize, Char.utf8Size, UInt32.ofNatCore, UInt32.toNat]
  split* <;> auto

theorem bsize_def s :
  String.bsize ⟨s⟩ = String.utf8ByteSizeAux s 0 := by
simp [String.bsize, utf8ByteSize]
generalize 0 = k
induction s generalizing k <;> auto

theorem le_bsize xs :
  List.length (String.toList xs) ≤ String.bsize xs  := by
rw [bsize_def]
trans _ </> apply le_utf8ByteSizeAux
simp [toList]; refl

protected def utf8ExtractAux₂ : List Char → Pos → Pos → List Char
  | [],    _, _ => []
  | c::cs, i, e =>
    if i = e
      then []
      else c :: String.utf8ExtractAux₂ cs (i + csize c) e

protected def utf8ExtractAux₁ : List Char → Pos → Pos → Pos → List Char
  | [],        _, _, _ => []
  | (c::cs), i, b, e =>
  -- | s@(c::cs), i, b, e => -- this prevents Lean from generating equations
  if i = b
    then String.utf8ExtractAux₂ (c::cs) i e
    else String.utf8ExtractAux₁ cs (i + csize c) b e

-- TODO: error message: failed to generate equality theorems for
-- `match` expression, support for array literals has not been
-- implemented yet
-- Bad error message
-- #eval Lean.Meta.getUnfoldEqnFor? ``String.utf8ExtractAux₁

theorem extract_def s :
  extract ⟨s⟩ b e = if b ≥ e then ⟨[]⟩ else ⟨String.utf8ExtractAux₁ s 0 b e⟩ := by
simp [extract]; split; rfl
apply congrArg
generalize 0 = p
induction s generalizing p
next => rfl
next x xs ih =>
  show ite _ _ _ = ite _ _ _
  split
  next =>
    clear ih
    show ite _ _ _ = ite _ _ _
    split; rfl
    apply congrArg
    generalize p + csize x = k
    induction xs generalizing k
    next => rfl
    next x' xs ih =>
      show ite _ _ _ = ite _ _ _
      split; rfl
      rw [ih]
  next =>
    rw [ih]
-- open Classical.em
-- #check Classical.em
-- #check byContradiction

@[simp]
theorem extract_nil :
  extract ⟨[]⟩ i j = "" := sorry

@[simp]
theorem extract_cons x xs :
  extract ⟨x :: xs⟩ i j = extract ⟨xs⟩ (i - csize x) (j - csize x) := by
simp [extract_def, String.utf8ExtractAux₁, String.utf8ExtractAux₂]
split
next h =>
  have h' : i - csize x ≥ j - csize x := sorry
  rw [if_pos h']
next h =>
  have h' : ¬ i - csize x ≥ j - csize x := sorry
  rw [if_neg h']; apply congrArg
  have h₂ : ¬ 0 = j := sorry
  byCases h₃ : 0 = i
  next =>
    rw [if_pos h₃, if_neg h₂]
  -- split*
next =>
  skip
  -- split
#exit

@[simp]
theorem drop_mk_nil :
  (String.mk []).drop n = String.mk [] := by
simp [drop, toSubstring, Substring.drop, Substring.toString, extract_def]
split <;> rfl

@[simp]
theorem toList_mk {x : List Char} :
  String.toList ⟨x⟩ = x := rfl

macro "falseHyp" h:ident : tactic =>
  `(apply Classical.contradiction $h)

@[simp]
theorem toList_append {s₀ s₁ : String} :
  (s₀ ++ s₁).toList = s₀.toList ++ s₁.toList :=
rfl

@[simp]
theorem extract_eq_nil {s} :
  extract s i i = "" := sorry


theorem extract_eq_self' {s} :
  extract s 0 i ++ extract s i s.bsize = s := by
cases s; next xs =>
-- generalize 0 = b
apply String.toList_inj; simp
-- #exit
induction xs
-- <;> simp [extract_def]
next => simp
next x xs ih =>
  cases i
  skip

#exit
next =>
  split*
  <;> next => rfl
next =>
  split
  next h =>
    have h := Nat.le_antisymm h (Nat.zero_le _)
    subst h; clear h
    rw [if_neg]
    next =>
      simp [String.utf8ExtractAux₁, String.utf8ExtractAux₂]
      rw [if_neg]
      skip
  skip
-- next => split <;> rfl
-- next xs ih =>
  -- split
-- next =>
  -- skip
  -- have := le_bsize ⟨xs⟩
--   simp at this
--   have := Nat.le_trans this h
--   have := Nat.le_antisymm this (Nat.zero_le _)
--   rw [List.length_eq_zero] at this
--   subst this; rfl
-- next xs h =>
--   simp [bsize, utf8ByteSize]
--   skip

@[simp]
theorem drop_zero (xs : String) :
  xs.drop 0 = xs := by
simp [drop, toSubstring, Substring.drop, Substring.toString, extract_eq_self, Substring.nextn]

-- #exit
@[simp]
theorem drop_mk_cons_succ (xs : List Char) :
  (String.mk <| x :: xs).drop n.succ =
  (String.mk xs).drop n := by
simp [drop, toSubstring, Substring.drop, Substring.toString, extract_def]
rw [if_neg, if_neg]
next =>
  congr; simp [Substring.nextn, Substring.next, String.utf8ExtractAux₁]
  -- rw [if_neg]
  split
  next h =>
    falseHyp h
    simp [bsize, utf8ByteSize]
    -- simp [String.utf8ByteSizeAux]
  -- rw [String.utf8ExtractAux₁._eq_2]
  -- simp only [String.utf8ExtractAux₁]
  skip

@[simp]
theorem toList_drop {s : String} :
  (s.drop n).toList = s.toList.drop n := by
cases s with | mk s =>
induction s generalizing n
<;> cases n <;> simp [*, List.drop]

@[simp]
theorem length_toList {s : String} :
  s.toList.length = s.length := rfl

theorem drop_append' {s₀ s₁ : String}
        (h : s₀.length = n) :
  (s₀ ++ s₁).drop n = s₁ := by
apply toList_inj; simp
rw [List.drop_append']
simp [h]

-- rw []
-- cases s₀ with | mk d =>
-- induction n genera

end String
