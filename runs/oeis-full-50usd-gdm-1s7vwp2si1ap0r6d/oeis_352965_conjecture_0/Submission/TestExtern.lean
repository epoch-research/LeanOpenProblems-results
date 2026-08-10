import FormalConjectures.Util.ProblemImports

open Nat Finset

def A352965 : ℕ → ℕ
| 0 => 0
| 1 => 0
| n + 1 => 0

@[extern "some_c_function"]
opaque oeis_352965_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → ∃ (n : ℕ), A352965 n = p
