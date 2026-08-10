import FormalConjectures.Util.ProblemImports

open Nat

lemma scaling_reduction (n : ℕ)
    (h : ∃ x y z w : ℕ,
      x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
      x ≥ y ∧
      (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt =
        x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) :
    ∃ x y z w : ℕ,
      x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 4 * n ∧
      x ≥ y ∧
      (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt =
        x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  rcases h with ⟨x, y, z, w, h1, h2, h3⟩
  use 2 * x, 2 * y, 2 * z, 2 * w
  refine ⟨?_, ?_, ?_⟩
  · calc
      (2 * x) ^ 2 + (2 * y) ^ 2 + (2 * z) ^ 2 + (2 * w) ^ 2 = 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
      _ = 4 * n := by rw [h1]
  · omega
  · have h_sq : (2 * x) ^ 2 + 8 * (2 * y) ^ 2 + 16 * (2 * z) ^ 2 = 4 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by ring
    rw [h_sq]
    have h_sqrt_prop : 4 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) =
        (2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) * (2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) := by
      have h_alg : 4 * ((x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) =
          (2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) * (2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt) := by ring
      rw [← h_alg]
      rw [h3]
    rw [h_sqrt_prop]
    rw [Nat.sqrt_eq]
