
-- import Libffi.Ffi.Data.Char
import Std.Data.HashMap
-- import Lib.Traversable
-- import Lib.Fold
-- #eval Char.genCat 'a'
-- #exit
def Array.hash [Hashable α] (ar : Array α) : UInt64 :=
ar.foldl
  (λ acc a => mixHash (Hashable.hash a) acc)
  (Hashable.hash 37)

namespace ForInStep

def get : ForInStep β → β
| yield r => r
| done r => r


def dup : ForInStep β → ForInStep (ForInStep β)
| yield r => yield <| yield r
| done r => done <| done r

end ForInStep

namespace System.FilePath
open System

inductive Root
| root | home | spec (s : String) | relative

inductive Dir (r : Root)
| tip
| dir (d : Dir r) (s : String)

structure File (r : Root) where
mkImpl ::
  path : Dir r
  base : String
  ext : String

-- def splitExt (fp : FilePath) : String × Option String :=
-- Id.run $ do
-- let ext :: fn ← fp.toString.splitOn "." |>.reverse
--     | return (fp.toString, none)
-- if fn.isEmpty then return (fp.toString, none)
-- else return (String.intercalate "." fn.reverse, some ext)

def hasExt (ext : String) (fp : FilePath) : Bool :=
extension fp = some ext

def filterDir (path : FilePath) (ext : String) :
    IO (Array FilePath) := do
  let ls ← readDir path
  return ls.filter (λ e => hasExt ext <| e |>.fileName)
         |>.map (. |>.fileName)

end System.FilePath

open IO.FS


structure ModuleName where
mkImpl ::
  components : Array String
  hash : UInt64
  hash_eq :
    hash = components.hash
deriving Repr

namespace ModuleName

instance : BEq ModuleName where
  beq x y := x.hash == y.hash && x.components == y.components

instance : Hashable ModuleName where
  hash | ⟨ar,h,_⟩ => h

def mk (s : Array String) : ModuleName :=
⟨ s.map <| String.map Char.toLower, _, rfl ⟩

def camelCase (m : ModuleName) : String :=
String.intercalate "."
  <| m.components.toList.map String.capitalize

def lowerCase (m : ModuleName) : String :=
String.intercalate "."
  <| m.components.toList

instance : ToString ModuleName where
  toString m := s!"import {m.camelCase}"

end ModuleName

def moduleName (name : String) : ModuleName :=
ModuleName.mk <| name.splitOn "." |>.toArray

namespace IO.FS.DirEntry
open IO.FS System System.FilePath

def toModuleName (dir : DirEntry) : ModuleName :=
ModuleName.mk
<| Option.getD (OptionM.run do
     let fn := FilePath.mk dir.fileName
     let base := components <| (← fn.parent)
     let last := (← fn.fileStem)
     let path := base ++ [last]
     return path.toArray )
   #[]

def importStmt (dir : DirEntry) (camelCase := true) : String :=
if camelCase then
  s!"import {dir.toModuleName |>.camelCase}"
else
  s!"import {dir.toModuleName |>.lowerCase}"

def ofFileName (dir fname : FilePath) : DirEntry :=
⟨dir,
  fname.toString.drop dir.toString.length
    |>.dropWhile ('/' == .)⟩

end IO.FS.DirEntry

section visitDirs
open System System.FilePath
variable [Monad m] [MonadLiftT IO m]

@[specialize]
partial def visitDir' [Inhabited β]
        (path : FilePath) (b : ForInStep β)
        (f : FilePath × Metadata →
                  ForInStep β →
                  m (ForInStep (ForInStep β))) :
  m (ForInStep (ForInStep β)) := do
  let m ← liftM <| metadata path
  let r ← f (path, m) b
  match r with
   | ForInStep.done r => return r.dup
   | ForInStep.yield r =>
     if ¬ (← liftM (isDir path : IO Bool)) then return r.dup
     let z ← forIn (← readDir path) r
       (λ fn b => visitDir' fn.path b f)
     return z.dup

@[inline]
def visitDir [Inhabited β]
  (path : FilePath) (b : β)
  (f : FilePath × Metadata →
                  β →
                  m (ForInStep β)) :
  m β := do
let r ← visitDir' path (ForInStep.yield b)
  λ fn b => (. |>.dup) <$> f fn b.get
return r.get.get

end visitDirs
open System IO.FS

instance [MonadLiftT IO m] :
         ForIn m FilePath (FilePath × Metadata) where
  forIn fp x f :=
    let inst : Inhabited _ := ⟨ x ⟩
    visitDir fp x f

instance [MonadLiftT IO m] :
         ForIn m DirEntry (DirEntry × Metadata) where
  forIn fp x f :=
    forIn fp.path x λ (fp', m) =>
      f (DirEntry.ofFileName fp.root fp', m)

open System.FilePath

def path : IO.FS.DirEntry :=
⟨"lib", "Lib/Data"⟩

def paths : Array IO.FS.DirEntry :=
#[⟨"lib", "Lib/Data"⟩, ⟨".", "Sat"⟩]

-- initialize leanFiles : Array System.FilePath ←
--   filterDir path "lean"

-- namespace Substring

-- def size (s : Substring) : Nat :=
-- s.bsize


-- end Substring


-- inductive Trie (α : Type)
-- | tip (x : α)
-- | pre (s : String) (h : s.length > 0) (t : Trie α)
-- | node (ar : Array (Char × Trie α))

-- namespace Trie

-- def longestPrefix' (r : String) (s s' : Substring) : String :=
-- if Hlt : ¬ s.isEmpty ∧ ¬ s'.isEmpty
--   then if s.get 0 = s'.get 0
--           then longestPrefix' (r.push <| r.get 0)
--                               (s.drop 1) (s'.drop 1)
--           else r
--   else r
-- termination_by measure λ ⟨_,s,_⟩ => s.bsize

-- def longestPrefix (i : Nat) (ar : Array (String × α)) : Nat :=
-- Id.run do
--   if h : ar.size > 0 then do
--     let mut j := ar.get ⟨0, h⟩ |>.1.length
--     for (s, _) in ar do
--       _
--   else _

-- def mkAux (ar : Array (String × α)) (i : Nat)
--     (h₀ : ∃ j, i ≤ (ar.get j |>.1).length) : Trie α

-- end Trie


def removeDataPrefix (n : ModuleName) : ModuleName :=
if n.components[:2] == #["lib", "data"] then
  ModuleName.mk <| #["lib"] ++ n.components[2:]
else n
open Std

inductive ImportToken (α : Type)
| importKw
| space (s : Substring)
| moduleName (mn : α)
deriving BEq, Repr

namespace ImportToken

@[specialize]
def traverse [Applicative m] (f : α → m β) :
  ImportToken α → m (ImportToken β)
| importKw => pure importKw
| space s => pure $ space s
| moduleName mn => moduleName <$> f mn

@[inline]
def map (f : α → β) : ImportToken α → ImportToken β :=
traverse (m := Id) f

abbrev RawTokens := Array <| ImportToken Substring

abbrev isSpace (c : Char) : Prop := c = ' '

-- instance : DecidablePred isSpace :=
-- λ c => inferInstanceAs

mutual
open ImportToken

partial def readWord (r : RawTokens) (i : Nat) (s : Substring) :
  RawTokens :=
if i = s.bsize
  then r.push <| moduleName s
else if isSpace <| s.get i then
  let lex₀ := s.extract 0 i
  let rest := s.extract i (s.stopPos - s.startPos)
  let tok := if lex₀ == "import".toSubstring
          then importKw
          else moduleName lex₀
  let r' := r.push tok
  readSpace r' (rest.next 0) rest
else
  readWord r (s.next i) s

partial def readSpace (r : RawTokens) (i : Nat) (s : Substring) :
  RawTokens :=
if i = s.bsize
  then r.push <| space s
else if isSpace <| s.get i
  then readSpace r (s.next i) s
else
  let lex₀ := s.extract 0 i
  let rest := s.extract i (s.stopPos - s.startPos)
  let tok := space lex₀
  let r' := r.push tok
  readWord r' (rest.next 0) rest

partial def splitLine (s : Substring) : RawTokens :=
if s.isEmpty then #[]
else if isSpace <| s.get 0
  then readSpace #[] 0 s
  else readWord #[] 0 s

end

-- def append

def render : ImportToken Substring → Substring
| importKw => "import".toSubstring
| moduleName n => n
| space s => s

-- #eval splitLine " import   Std.Data.HashMap ".toSubstring

end ImportToken
-- #eval ' '.isAlpha

inductive ImportLine (α : Type)
| singleLine (pre : α) (comment : Substring)
| openMultiline (pre : α) (comment : Substring)
| comment (comment : Substring)
| closeMultiline (comment : Substring) (post : α)
| notImport
deriving Inhabited, Repr

abbrev ImportLine' := ImportLine Substring

namespace ImportLine

@[specialize]
def traverse [Applicative m] (f : α → m β) :
  ImportLine α → m (ImportLine β)
| singleLine pre c =>
  (singleLine . c) <$> f pre
| openMultiline pre c =>
  (openMultiline . c) <$> f pre
| comment c => pure $ comment c
| closeMultiline c post =>
  (closeMultiline c .) <$> f post
| notImport => pure notImport

@[inline]
def map (f : α → β) (x : ImportLine α) :
    ImportLine β :=
traverse (m := Id) f x

def openComment : ImportLine α → Bool
| openMultiline _ _ => true
| _ => false

def closeComment : ImportLine α → Bool
| closeMultiline _ _ => true
| _ => false

def render [ToString α] : ImportLine α → String
| singleLine pre c => toString pre ++ c.toString
| openMultiline pre c => toString pre ++ c.toString
| closeMultiline c pre => c.toString ++ toString pre
| comment c => c.toString
| notImport => ""

def isImport : ImportLine α → Bool
| notImport => false
| _ => true

end ImportLine

section subst

variable (d : HashMap ModuleName ModuleName)
-- def splitComment

partial def readComment
  (line : String) (commentOpen : Bool) : ImportLine' :=
if commentOpen ∨
   line.isEmpty ∨
   "import".isPrefixOf line ∨
   " ".isPrefixOf line ∨
   "--".isPrefixOf line then
  if commentOpen then
    let rec loop (it : String.Iterator) : ImportLine' :=
      if !it.hasNext then
        ImportLine.comment it.s.toSubstring
      else
        let it' := it.next
        if it.curr = '-' then
          if it'.hasNext ∧ it'.curr = '/'
            then
              let it'' := it'.next
              let s := it.s.toSubstring
              ImportLine.closeMultiline
                (s.extract 0 it''.i)  (s.extract it''.i s.stopPos)
            else loop it'
        else loop it'
    loop line.mkIterator
  else
    let rec loop' (it : String.Iterator) : ImportLine' :=
      if !it.hasNext then
        ImportLine.singleLine it.s.toSubstring "".toSubstring
      else
        let it' := it.next
        if it.curr = '/' then
          if it'.hasNext ∧ it'.curr = '-'
            then
              let s := it.s.toSubstring
              ImportLine.openMultiline
                (s.extract 0 it.i)  (s.extract it.i s.stopPos)
            else loop' it'
        else if it.curr = '-' then
          if it'.hasNext ∧ it'.curr = '-' then
            let s := it.s.toSubstring
            ImportLine.singleLine
              (s.extract 0 it.i)  (s.extract it.i s.stopPos)
          else loop' it'
        else loop' it'
    loop' line.mkIterator
else ImportLine.notImport

def replaceModuleName (s : Substring) : Substring :=
let mid := moduleName s.toString
match d.find? mid with
| some mid => mid.camelCase.toSubstring
| none => s

def join (ar : Array Substring) : Substring :=
ar.foldl (λ acc s => acc ++ s.toString) "" |>.toSubstring

def rewriteLine
  (line : String) (commentOpen : Bool) : IO ImportLine' := do
let imp := readComment line commentOpen
let imp := imp.map ImportToken.splitLine
let imp := imp.map <| Array.map <| ImportToken.map (replaceModuleName d)
return imp.map <| _root_.join ∘ Array.map ImportToken.render

def rewriteImports' (file to : FilePath) : IO Unit := do
  let lines ← IO.FS.lines file
  let h ← IO.FS.Handle.mk to Mode.write
  let mut i := 0
  let mut comment := false
  for ln in lines do
    let x ← rewriteLine d ln comment
    unless x.isImport do
      break
    if comment then
      comment := ! x.closeComment
    else
      comment := x.openComment
    h.putStrLn <| x.render
    i := i + 1
  for ln in lines[i:] do
    h.putStrLn ln

partial def copyFile (dst src : FilePath) : IO Unit := do
let hsrc ← Handle.mk src Mode.read false
let hdst ← Handle.mk dst Mode.write false
let rec loop : IO Unit := do
  let ln ← hsrc.getLine
  if ln.isEmpty then return ()
  else do
    hdst.putStr ln
    loop
loop

def moveFile (dst src : FilePath) : IO Unit := do
copyFile dst src
removeFile src

def rewriteImports (file : FilePath) : IO Unit := do
let to := file.withExtension "lean.tmp"
rewriteImports' d file to
moveFile file to

end subst

partial def gitRootAux (p : FilePath) : IO (Option FilePath) := do
if (← isDir (p / ".git")) then return p
else
  match p.parent with
  | some x => gitRootAux x
  | none => return none

def gitRoot : IO (Option FilePath) := do
gitRootAux (← IO.currentDir)

def main : IO Unit := do
let ls ← System.FilePath.readDir path.path
let mut i := 0
let mut subst := Std.mkHashMap
for (p@⟨root, fn⟩, _) in path do
  if hasExt "lean" fn then
    let m := p.toModuleName
    subst := subst.insert (removeDataPrefix m) m
for (p, _) in path do
  if hasExt "lean" p.fileName then
    IO.println p.path
    rewriteImports subst p.path
