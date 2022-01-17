
def parseNat (x : String) : IO Nat :=
match x.toNat? with
| none => throw (IO.userError "parsing error")
| some n => pure n

def lines (x : String) : Array String :=
(x.splitOn "\n").toArray

def curl (url filename : String) : IO Unit := do
let out ← IO.Process.run { cmd := "curl", args := #[url] }
IO.FS.writeFile filename out

def inputUrl (day : String) : String :=
let d := day.dropWhile (not ∘ Char.isDigit)
      |>.takeWhile Char.isDigit
s!"https://adventofcode.com/2021/day/{d}/input"

def escapePath (fp : System.FilePath) : String :=
fp.toString
-- String.intercalate "\\ "
--  <| fp.toString.splitOn " "

def moveFile (src dest : System.FilePath) : IO Unit := do
if ¬ (← System.FilePath.pathExists src) then
  throw <| IO.userError s!"Path does not exist {src}"
IO.FS.writeFile dest (← IO.FS.readFile src)
IO.FS.removeFile src
-- let { stdout, stderr, exitCode } ← IO.Process.output {
--         cmd := "mv",
--         args := #[escapePath src, escapePath dest] }
-- if exitCode ≠ 0 then
--   throw <| IO.userError s!"mv failed:\n{stderr}"


def copyFile (src dest : System.FilePath) : IO Unit := do
let { stdout, stderr, exitCode } ← IO.Process.output {
        cmd := "cp",
        args := #[escapePath src, escapePath dest] }
if exitCode ≠ 0 then
  throw <| IO.userError s!"cp failed:\n{stderr}"

def checkInput (day file : String) : IO Unit := do
let some home ← IO.getEnv "HOME"
    | throw <| IO.userError s!"variable not found: HOME"
let source := s!"{home}/Downloads/input.txt"
-- let dest := s!"{home}/file"
let dest := s!"{(← IO.currentDir)}/{file}"
if ¬ (← System.FilePath.pathExists dest) then
  IO.println dest
  if (← System.FilePath.pathExists source) then
    moveFile source dest
    println! "false"
  else
    throw <| IO.userError s!"input file not found at {source}"
else println! "true"
