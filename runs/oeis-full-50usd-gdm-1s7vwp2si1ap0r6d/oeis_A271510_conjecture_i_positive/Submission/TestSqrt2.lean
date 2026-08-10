import FormalConjectures.Util.ProblemImports

open Nat

theorem test_p2 : ∃ x y z w,
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 2 ∧
    x ≥ y ∧
    (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt =
      x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  use 0, 0, 1, 1
  refine ⟨by decide, by decide, ?_⟩
  change (4 * 4).sqrt * (4 * 4).sqrt = 4 * 4
  rw [Nat.sqrt_eq]
