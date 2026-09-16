import Mathlib

lemma div_ineq_mod (u v M : ℕ) (hu : u < M) (hv : v < M) (huv : v ≤ 4 * u) :
    (4 * u - v) / M + (3 * u) / M + (2 * u) / M ≤ (8 * u - 2 * v) / M + (8 * v) / M + u / M := by
  sorry
