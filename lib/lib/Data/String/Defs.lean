
namespace String

def padding (margin : Nat) (s : String) : String :=
s ++ Nat.repeat (" " ++ .) (margin - s.length) ""

end String
