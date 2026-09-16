import Mathlib

lemma test_case (u v M : ℕ) (hM : 0 < M) (huv : v ≤ 4 * u)
  (hk1 : 10 * M ≤ 24 * u) (hk2 : 24 * u < 11 * M)
  (hj1 : 5 * M ≤ 24 * v) (hj2 : 24 * v < 6 * M) :
  M ≤ 4 * u - v := by
  omega
