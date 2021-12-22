
def parseNat (x : String) : IO Nat :=
match x.toNat? with
| none => throw (IO.userError "parsing error")
| some n => pure n

def lines (x : String) : Array String :=
(x.splitOn "\n").toArray
