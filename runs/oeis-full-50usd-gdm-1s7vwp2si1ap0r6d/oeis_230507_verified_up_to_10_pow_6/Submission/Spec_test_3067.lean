import FormalConjectures.Util.ProblemImports
open Nat

example : ∀ x ∈ [2, 2, 2, 2, 3067, 3067, 3067], x.Prime := by
  simp; exact ⟨by norm_num, by norm_num⟩
