
namespace Char

instance : Hashable Char where
  hash c := hash c.toNat

end Char
