
namespace Option

def elim {α β} (x : β) (f : α → β) : Option α → β
| none => x
| some x => f x

end Option
