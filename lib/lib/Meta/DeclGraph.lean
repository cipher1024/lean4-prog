
-- import Lean.Meta.Eqns
import Lean.Elab.Declaration
import Lib.Data.HashMap
import Lib.Data.Prod.Defs

-- open Lean.Meta
open Lean.Expr
-- open Lean.Elab.Command
-- open Lean.Elab.Term
-- open Lean.Elab.Frontend
open Lean

def isEdgeTo (e : Expr) (n' : Name) : Bool :=
match e with
| forallE _ d b m => isEdgeTo b n'
| _ => e.isAppOf n'

def isEdge' (e : Expr) (n n' : Name) : Bool :=
match e with
| forallE _ d b m =>
     d.isAppOf n && isEdgeTo b n'
  || isEdge' b n n'
| _ => false

def isEdge (e : Expr) (n n' : Name) : Bool :=
isEdge' e.consumeMData n n'

def listEdges' (e : Expr) (noProps : Bool) :
  Option (Name × List (Name × Name)) := do
match e with
| forallE _ d b m => do
  let (to, es) ← listEdges' b noProps
  match constName? d.getAppFn with
  | some n => pure (to, (n, to) :: es)
  | none => pure (to, es)
| _ => do
  let n ← constName? e.getAppFn
  if n == ``MonadLift ||
     n == ``MonadLiftT ||
     n == ``MonadFunctor ||
     n == ``MonadFunctorT then
    let args := getAppRevArgs e
    let x₁ := args[0]
    let x₀ := args[1]
    let to ← constName? x₁.getAppFn
    let from_ ← constName? x₀.getAppFn
    pure (to, [(from_, to)])
  else
    pure (n, [])

def listEdges (e : Expr) (noProps := true) : List (Name × Name) :=
  match listEdges' e noProps with
  | none => []
  | some (_, es) => es

open Std

structure Queue (α : Type _) where
  front : List α := []
  back : List α := []

namespace Queue

def push (q : Queue α) (x : α) : Queue α :=
{ q with back := x :: q.back }

def pop (q : Queue α) : Option (α × Queue α) :=
let q' :=
  if q.front.isEmpty then
    { front := q.back.reverse
      back := [] }
  else q
match q'.front with
| [] => none
| x :: xs =>
  let q' :=
    { q' with front := xs }
  (x, q')

end Queue


abbrev Graph := Std.HashMap Name (Array (Name × Name))


namespace Graph

def Path := List Name
  deriving BEq, Hashable, ToString

def mk : Graph := Std.mkHashMap

def addEdges (G : Graph) (ls : List (Name × Name × Name)) : Graph :=
ls.foldl (λ G (e, v₀, v₁) => G.modifyD v₀ #[] (·.push (e, v₁))) G

variable (G : Graph)

def successors (v : Name) : Array (Name × Name) :=
G.findD v #[]

partial def listPaths' (n' : Name) (q : Queue (Name × List Name))
    (visited : HashSet Name) (acc : Array Path) : Array Path :=
match q.pop with
| none => acc
| some ((v₀, p), q) => Id.run do
  let mut q := q
  let mut acc := acc
  let mut visited := visited
  for (e, v₁) in G.successors v₀ do
    let p' := e :: p
    if v₁ == n' then
      acc := acc.push p'.reverse
    else if ¬ visited.contains v₀ then
      q := q.push (v₁, p')
      visited := visited.insert v₁
  listPaths' n' q (visited.insert v₀) acc

def listPaths (n n' : Name) : Array Path :=
listPaths' G n'
  (Queue.push {} (n, []))
  (HashSet.insert {} n)
  #[]

end Graph

def findPath (n n' : Name) :  MetaM (List Name) := do
let env ← getEnv
let n  ← resolveGlobalConstNoOverload (mkIdent n)
let n' ← resolveGlobalConstNoOverload (mkIdent n')
let ls : List Name :=
  env.constants.fold (λ cs decl c =>
    if isEdge c.type n n' then decl :: cs
    else cs ) []
return ls

def isPrivate : Name → Bool
| Name.str Name.anonymous s .. => s == "_private"
| Name.str n .. => isPrivate n
| Name.num n .. => isPrivate n
| Name.anonymous => false

def hasUnderscore : Name → Bool
| Name.str _ s .. => "_".isPrefixOf s
| _ => false

def isThm : ConstantInfo → Bool
| ConstantInfo.thmInfo _ => true
| _ => false

def mkDeclGraph (inverted := false) (noLoops := true)
  (noProps := true) : MetaM Graph := do
let env ← getEnv
let G := Graph.mk
return env.constants.fold (λ G decl c =>
       if hasUnderscore decl || isPrivate decl
       then G
       else Id.run do
         let mut edges := listEdges c.type (noProps := noProps)
         if noProps && isThm c then
           edges := []
         if noLoops then
           edges := edges.filter λ (n,n') => n != n'
         if inverted then
           edges := edges.map Prod.swap
         G.addEdges <| List.map (decl, .) edges )
    G

open Lean.Elab
open Lean.Elab.Term
open Lean.Elab.Command
-- open Lean.Elab.Frontend

-- def test : MetaM (Array (List String)) := do
-- let G ← mkDeclGraph
-- let paths := G.listPaths ``FrontendM ``IO
-- -- let paths := G.listPaths ``CommandElabM ``FrontendM
-- let paths := G.listPaths ``MetaM ``CoreM
-- -- let paths := G.listPaths ``CoreM ``MetaM
-- -- let paths := G.listPaths ``MetaM ``CommandElabM
-- -- let paths := G.listPaths ``CoreM ``CommandElabM
-- return Array.map (List.map toString) paths

def test' : MetaM (Array String) := do
let G ← mkDeclGraph
let edges := G.successors ``CommandElabM
return edges.map λ (n, _) => toString n

def nameLt (x y : Name) : Bool :=
x.components.map toString < y.components.map toString

def sortNames : Array Name → Array Name :=
Array.qsort (lt := nameLt)

def succCmd (x : Name) : MetaM Unit := do
let G ← mkDeclGraph
let fns := G.successors x
  |>.foldl (λ s (n, _) => HashSet.insert s n) {}
-- for fn in fns.toArray do
for fn in sortNames fns.toArray do
  let c ← mkConstWithLevelParams fn
  let t ← Meta.inferType c
  println!"{c} : {← Meta.ppExpr t}"

elab "#succ" x:ident : command => do
  let x ← resolveGlobalConstNoOverload x
  liftCoreM <| succCmd x |>.run'

def predCmd (x : Name) : MetaM Unit := do
let G ← mkDeclGraph (inverted := true)
let fns := G.successors x
  |>.foldl (λ s (n, _) => HashSet.insert s n) {}
for fn in sortNames fns.toArray do
  let c ← mkConstWithLevelParams fn
  let t ← Meta.inferType c
  println!"{c} : {← Meta.ppExpr t}"

elab "#pred" x:ident : command => do
  let x ← resolveGlobalConstNoOverload x
  liftCoreM <| predCmd x |>.run'

def findPathCmd (x y : Name) : MetaM Unit := do
let i : Hashable Graph.Path := inferInstance
let G ← mkDeclGraph
let paths := G.listPaths x y
  |>.foldl HashSet.insert mkHashSet
println!"from {x} to {y}"
for p in paths.toArray do
  println!"- {p}"

elab "#path" x:ident y:ident : command => do
  let x ← resolveGlobalConstNoOverload x
  let y ← resolveGlobalConstNoOverload y
  liftCoreM <|
    findPathCmd x y |>.run'

elab "#fullname" x:ident : command => do
  let x := x.getId
  let env ← getEnv
  let ar : Array Name := env.constants.fold
    (λ ar n _ => if x.isSuffixOf n
      then ar.push n
      else ar ) #[]
  println!"Full name of {x}"
  if ar.isEmpty then
    println!"no decl found"
  else
    for n in ar do
      println!"· {n}"

elab "#find" "prefix" x:ident : command => do
  let x := x.getId
  let env ← getEnv
  let ar : Array Name := env.constants.fold
    (λ ar n _ =>
      if let Name.str _ s .. := n
      then if x.getString!.isPrefixOf s
        then ar.push n
        else ar
      else ar ) #[]
  println!"Full name of {x}"
  if ar.isEmpty then
    println!"no decl found"
  else
    for n in ar do
      println!"· {n}"
