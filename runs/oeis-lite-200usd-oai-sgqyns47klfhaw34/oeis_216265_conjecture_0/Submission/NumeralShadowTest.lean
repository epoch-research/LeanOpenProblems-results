import FormalConjectures.Util.ProblemImports

namespace Shadow
local instance high13 : OfNat ℕ 13 := ⟨1000000⟩
#eval (13 : ℕ)
example : (13 : ℕ) = 13 := rfl
-- if local instance took effect, this rfl would fail or print 1000000
end Shadow
