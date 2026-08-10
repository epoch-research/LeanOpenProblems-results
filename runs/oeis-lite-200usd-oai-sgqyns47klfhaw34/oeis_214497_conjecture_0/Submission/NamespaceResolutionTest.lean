import FormalConjectures.Util.ProblemImports

namespace Fake
namespace Nat
def Prime (_ : ℕ) : Prop := True
end Nat

-- Does Nat.Prime refer to Fake.Nat.Prime here?
example : Nat.Prime 0 := by trivial
#check Nat.Prime
end Fake

namespace Nat
-- In namespace Nat, check resolution
#check Nat.Prime
#check _root_.Nat.Prime
end Nat
