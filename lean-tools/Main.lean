import Lake.Config.Load
import Lean.PrettyPrinter.Delaborator.Basic
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
<| Option.getD (do
     let fn := FilePath.mk dir.fileName
     let base := components <| (← fn.parent)
     let last := (← fn.fileStem)
     let path := base ++ [last]
     return path.toArray)
   #[]

def importStmt (dir : DirEntry) (camelCase := true) : String :=
if camelCase then
  s!"import {dir.toModuleName |>.camelCase}"
else
  s!"import {dir.toModuleName |>.lowerCase}"

def ofFilePath (dir fname : FilePath) : DirEntry :=
⟨dir,
  let abs := dir.isAbsolute
  let dir := dir.components.erase "."
  let fname := fname.components.erase "."
  String.intercalate "/" <| fname.drop dir.length⟩

end IO.FS.DirEntry

section visitDirs
open System System.FilePath
variable [Monad m] [MonadLiftT IO m] [MonadExcept ε m]

def attempt (x : m α) : m (Option α) :=
try some <$> x catch _ => return none

@[specialize]
partial def visitDir' [Inhabited β]
        (path : FilePath) (b : ForInStep β)
        (f : FilePath × Metadata →
                  ForInStep β →
                  m (ForInStep (ForInStep β))) :
  m (ForInStep (ForInStep β)) := do
  let some m ← attempt <| liftM <| metadata path
      | return b.dup
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

instance [MonadLiftT IO m] [MonadExcept ε m] :
         ForIn m FilePath (FilePath × Metadata) where
  forIn fp x f :=
    let inst : Inhabited _ := ⟨ x ⟩
    visitDir fp x f

instance [MonadLiftT IO m] [MonadExcept ε m] :
         ForIn m DirEntry (DirEntry × Metadata) where
  forIn fp x f :=
    forIn fp.path x λ (fp', m) =>
      f (DirEntry.ofFilePath fp.root fp', m)

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

abbrev isSpace (c : Char) : Prop := c.isWhitespace

-- instance : DecidablePred isSpace :=
-- λ c => inferInstanceAs

mutual
open ImportToken

partial def readWord (r : RawTokens) (i : String.Pos) (s : Substring) :
  RawTokens :=
if i.byteIdx = s.bsize
  then r.push <| moduleName s
else if isSpace <| s.get i then
  let lex₀ := s.extract 0 i
  let rest := s.extract i (s.stopPos - s.startPos)
  let tok := if lex₀ == "import".toSubstring
          then importKw
          else moduleName lex₀
  let r' := r.push tok
  readSpace r' (rest.next {}) rest
else
  readWord r (s.next i) s

partial def readSpace (r : RawTokens) (i : String.Pos) (s : Substring) :
  RawTokens :=
if i.byteIdx = s.bsize
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

def rewriteImports' (file to : FilePath) : IO Bool := do
  let lines ← IO.FS.lines file
  let h ← IO.FS.Handle.mk to Mode.write
  let mut changed := false
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
    let out := x.render
    changed := changed || (out != ln)
    h.putStrLn out
    i := i + 1
  if changed then
    for ln in lines[i:] do
      h.putStrLn ln
    return true
  else return false

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
let changed ← rewriteImports' d file to
if changed then
  moveFile file to
else
  removeFile to

end subst

def absolute (fp : FilePath) : IO FilePath := do
return normalize ((← IO.currentDir) / fp)

partial def findParentAux
        (path : FilePath) (p : FilePath → IO Bool) :
  IO (Option FilePath) := do
if (← p path) then return path
else
  match path.parent with
  | some x => findParentAux x p
  | none => return none

def findParent (p : FilePath → IO Bool)
    (path : Option FilePath := none) :
  IO (Option FilePath) := do
let path ← match path with
           | none => IO.currentDir
           | some p => absolute p
findParentAux path p

def gitRoot (path : Option FilePath := none) : IO (Option FilePath) := do
findParent (λ p => isDir (p / ".git")) path

def pathToLakefile (path : Option FilePath := none) : IO (Option FilePath) := do
findParent (λ p => pathExists (p / "lakefile.lean")) path

def lakeRoot (path : Option FilePath := none) : IO (Option FilePath) := OptionT.run do
let p ← pathToLakefile path
let cfg ← Lake.Package.load p []
return cfg.srcDir

namespace System.FilePath

def replaceRoot (src dst fn : FilePath) : FilePath :=
dst / (fn.toString.drop src.toString.length |>.dropWhile
        (pathSeparators.elem .))

end System.FilePath

namespace IO.FS.DirEntry

def replaceRoot (src dst : FilePath) (fn : DirEntry) : FilePath :=
System.FilePath.replaceRoot src dst fn.path

end IO.FS.DirEntry

/-- Return true iff `p` is a suffix of `s` -/
def String.isSuffixOf (p : String) (s : String) : Bool :=
  substrEq p 0 s ⟨s.endPos.byteIdx - p.endPos.byteIdx⟩ p.endPos.byteIdx

def System.FilePath.isInvisible (p : FilePath) : Bool :=
".".isPrefixOf <| p.fileStem |>.getD ""

namespace Move

protected def usage : String := "
Usage:
  mv source target
  mv source ... directory
"

inductive Cmd
| rename (n1 n2 : FilePath)
| move (fs : Array FilePath) (to : FilePath)

open FilePath

def mkModuleName (fn : FilePath) (root : Option FilePath := none) : IO ModuleName := do
let some p ← match root with
             | none => lakeRoot fn
             | some p => pure <| some p
    | throw <| IO.userError s!"{fn} is not in a 'lake' project"
return DirEntry.ofFilePath p fn |>.toModuleName

def liftOpt (msg : String) : Option α → IO α
| none => throw <| IO.userError msg
| some x => pure x

def getParent (fn : FilePath) : IO FilePath :=
liftOpt s!"{fn} does not have a parent" fn.parent

def getStem (fn : FilePath) : IO String :=
liftOpt s!"{fn} does not have a parent" fn.fileStem

def moduleNames (fn to : FilePath) (parent : Bool) :
    IO (Array (ModuleName × ModuleName)) := do
let fn' ← absolute fn
let to' ← absolute to
let some root ← lakeRoot <| some fn'
  | throw <| IO.userError s!"lakefile not found for {fn}"
let some to   ← lakeRoot to'
  | throw <| IO.userError s!"lakefile not found for {to}"
if (← isDir fn') then
  let fn'' ← if parent then getParent fn' else pure fn'
  let mut r := #[]
  for ⟨p, _⟩ in fn' do
    if hasExt "lean" p ∧ ¬ p.isInvisible then
      let p' := replaceRoot fn'' to' p
      let m  ← mkModuleName p root
      let m' ← mkModuleName p' to
      r := r.push (m, m')
  return r
else
  let s ← getStem fn'
  let p' := if parent then to' / s else to'
  let m  ← mkModuleName fn' root
  let m' ← mkModuleName p' to
  return #[(m, m')]

def Cmd.dest : Cmd → FilePath
| rename n1 n2 => n2
| move n1 n2 => n2

def Cmd.createPath (c : Cmd) : IO Unit := do
if ¬ (← c.dest.pathExists) then
  if hasExt "lean" c.dest then
    let p ← liftOpt s!"{c.dest} does not have a parent"
        <| c.dest.parent
    createDirAll p
  else
    createDirAll c.dest

def Cmd.renameMap : Cmd → IO (HashMap ModuleName ModuleName)
| rename n1 n2 => do
  let mut r := mkHashMap
  for (m, m') in ← moduleNames n1 n2 (parent := false) do
    r := r.insert m m'
  return r
| move fs to => do
  let mut r := mkHashMap
  for fn in fs do
    for (m, m') in ← moduleNames fn to (parent := true) do
      r := r.insert m m'
  return r

def checkFilePath (fn : String) : IO FilePath := do
let fn := FilePath.mk fn
unless ← pathExists fn do
  throw <| IO.userError s!"'{fn}' is not a valid path"
return fn

def mkCmd (ar : Array String) : IO Cmd := do
unless ar.size ≥ 2 do throw <| IO.userError Move.usage
if ar.size > 2 then
  let dir := ar.get! (ar.size - 1)
  let srcs ← ar[:ar.size-1].toArray.mapM checkFilePath
  let dir ←
    if ← pathExists dir then
      unless ← isDir dir do throw <| IO.userError Move.usage
      pure <| FilePath.mk dir
    else
      let dir := FilePath.mk dir
      createDirAll dir
      pure dir
  return Cmd.move srcs dir
else
  let src ← checkFilePath ar[0]
  let dst := FilePath.mk ar[1]
  if ← pathExists dst then
    if "/".isSuffixOf dst.toString ∧ (← isDir dst) then
      return Cmd.move #[src] dst
    else
      throw <| IO.userError
        s!"{dst} exists and cannot be replaced by {src}"
  else
    return Cmd.rename src dst

end Move

abbrev CmdLineFlag (short : String) (long : Option String) (descr : String) := Bool

structure Flags where
  traceCmd :
    CmdLineFlag "-c" none
    "tracing: print command" := false
  traceSubst :
    CmdLineFlag "-s" none
    "tracing: print module renaming" := false
  traceRoot :
    CmdLineFlag "-r" none
    "tracing: print command" := false
  dryRun :
    CmdLineFlag "-d" none
    "dry run: calculate parameter perform no action" := false
  forward : Array String := #[]
                           -- array of -f, -i, -n, -v, -k
  deriving Repr, Inhabited

partial def parseFlagsAux (fl : Flags) (ar : Subarray String) :
  Flags × Array String :=
if ar.start = ar.stop then
  (fl, #[])
else
  let hd := ar.as.get! ar.start
  if hd = "-c" then
    parseFlagsAux { fl with traceCmd := true } ar.popFront
  else if hd = "-s" then
    parseFlagsAux { fl with traceSubst := true } ar.popFront
  else if hd = "-r" then
    parseFlagsAux { fl with traceRoot := true } ar.popFront
  else if hd = "-d" then
    parseFlagsAux { fl with dryRun := true } ar.popFront
  else if #["-f", "-i", "-n", "-v", "-k"].elem hd then
    parseFlagsAux
      { fl with forward := fl.forward.push hd }
      ar.popFront
  else
    (fl, ar)

def parseFlags := parseFlagsAux {}

def parseCmdLine (args : Array String) : IO (Flags × Move.Cmd) :=
if args.size > 0 ∧ args.get! 0 = "mv" then
  let (flags, args) := parseFlags args[1:]
  (flags, .) <$> Move.mkCmd args
else
  throw <| IO.userError Move.usage

/--  -/
def Move.Cmd.scope : Move.Cmd → IO (Bool × FilePath)
| Move.Cmd.move fs to => do
  let mut git ← gitRoot to
  let mut lake ← lakeRoot to
  unless lake.isSome do
    throw <| IO.userError s!"Lake project not found for {to}"
  for fn in fs do
    match ← gitRoot (some fn) with
    | some p => if git != some p then git := none
    | none => git := none
    match ← lakeRoot (some fn) with
    | some p => if lake != some p then lake := none
    | none => lake := none
  match git, lake with
  | some p, _ => return (true, p)
  | none, some p => return (false, p)
  | none, none =>
    throw <| IO.userError s!"No common git or lake project found"
| Move.Cmd.rename fn to => do
  let fnGit ← gitRoot fn
  let fnLake ← lakeRoot fn
  let toGit ← gitRoot to
  let toLake ← lakeRoot to
  if fnGit.isSome ∧ fnGit == toGit then
    return (true, fnGit.getD "")
  if fnLake.isSome ∧ fnLake == toLake then
    return (true, fnGit.getD "")
  throw <| IO.userError s!"No common git or lake project found"

def Move.Cmd.args (cmd : Move.Cmd) (opts : Flags)
    (useGit : Bool) : IO.Process.SpawnArgs :=
let args :=
  match cmd with
  | Move.Cmd.rename fn to => #[fn.toString, to.toString]
  | Move.Cmd.move fs to => fs.push to |>.map ToString.toString
if useGit
  then { cmd := "git", args := #["mv"] ++ opts.forward ++ args }
  else { cmd := "mv", args := opts.forward ++ args }

def Cmd.run (args : Array String) : IO Unit := do
let (flags, c) ← parseCmdLine args
let subst ← c.renameMap
c.createPath
let (useGit, scope) ← c.scope
let args := c.args flags useGit
if flags.traceCmd then
  let cmd := String.intercalate " "
    <| args.cmd :: args.args.toList
  println!"cmd: {cmd}"
if flags.traceRoot then
  println!"root: {scope}"
if flags.traceSubst then
  println!"substitution:"
  for (m, m') in subst.toList do
    println!"  * {m.camelCase} := {m'.camelCase}"
if !flags.dryRun then
  discard <| IO.Process.output args
  for (p, _) in scope do
    if hasExt "lean" p ∧
       ¬ p.isInvisible then
      rewriteImports subst p

def main (args : List String) : IO Unit := do
try
  Cmd.run args.toArray
catch e =>
  IO.eprintln e
