
import Advent.IO

namespace (>>>FILE_SANS<<<)

def examples :=
""

def inputFileName := "Advent/(>>>FILE_SANS<<<)_input.txt"

initialize do
  checkInput "(>>>FILE_SANS<<<)" inputFileName

def parseInput (lines : Array String) : IO Unit := pure ()

def main : IO Unit := do
-- let ar ← parseInput <| (← IO.FS.lines inputFileName)
let ar ← parseInput <| (← lines examples)
IO.println "Hello world"

#eval main

end (>>>FILE_SANS<<<)