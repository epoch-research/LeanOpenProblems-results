import Mathlib

lemma div_bound (u v M : ℤ) (hM : 0 < M) (hu : 0 ≤ u) (huM : u < M) (hv : 0 ≤ v) (hvM : v < M) :
    -1 ≤ (4 * u - v) / M ∧ (4 * u - v) / M ≤ 3 := by
  sorry
