import FormalConjectures.Util.ProblemImports

open Nat Finset

unsafe def unsafe_proof (n : ℕ) : 1 < n → 1 + 1 = 2 := by
  intro
  rfl

-- Can a safe theorem call an unsafe def?
theorem safe_theorem (n : ℕ) (hn : 1 < n) : 1 + 1 = 2 := by
  exact unsafe_proof n hn
