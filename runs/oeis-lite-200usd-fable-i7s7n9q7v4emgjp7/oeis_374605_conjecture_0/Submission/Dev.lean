import FormalConjectures.Util.ProblemImports

/- Development scaffold for oeis_374605_conjecture_0 -/

open Finset

namespace A374605

/-- The generalized binomial coefficient `[z^N] (1+z)^m` for `m : ℤ`, `N : ℕ`. -/
def gbin (m : ℤ) (N : ℕ) : ℤ := ∏ i ∈ range N, (m - i) / N.factorial

-- hmm, integer division is wrong; use Ring.choose? Check what Mathlib has:
-- `Int.negSucc`? There is `Ring.choose` in Mathlib for binomial coefficients in a ring.
end A374605
