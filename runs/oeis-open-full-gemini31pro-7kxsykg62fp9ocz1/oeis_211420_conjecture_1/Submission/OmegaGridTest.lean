import Mathlib

lemma test_case (u v M : ℕ) (hM : 0 < M) (huv : v ≤ 4 * u)
  (hk1 : 10 * M ≤ 24 * u) (hk2 : 24 * u < 11 * M)
  (hj1 : 5 * M ≤ 24 * v) (hj2 : 24 * v < 6 * M) :
  (4 * u - v) / M + (3 * u) / M + (2 * u) / M ≤ (8 * u - 2 * v) / M + (8 * v) / M + u / M := by
  have q1 : (4 * u - v) / M = 1 := by
    -- to prove it is 1, we need M <= 4u - v < 2M
    -- 24M <= 96u - 24v < 48M
    -- 96u >= 40M, 24v < 6M => 96u - 24v > 34M >= 24M.
    sorry
  sorry
