import FormalConjectures.Util.ProblemImports

open Finset

set_option maxRecDepth 1000000000

theorem test_trivial : ∀ (n : ℕ), n ∈ Finset.Ioc 0 1000000000 → 0 < 1 := by
  decide

