import Mathlib

lemma test_strategy2 (u v M : ℤ) (hM : 0 < M) (hu : 0 ≤ u) (huM : u < M) (hv : 0 ≤ v) (hvM : v < M)
  (q1 : ℤ) (hq1 : q1 * M ≤ 4 * u - v ∧ 4 * u - v < (q1 + 1) * M)
  (hq_val : q1 = 2) :
  2 * M ≤ 4 * u - v := by
  subst hq_val
  omega
