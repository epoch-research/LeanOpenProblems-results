import Mathlib

lemma test (u M : ℕ) (hM : 0 < M) (h1 : 16 * M ≤ 24 * u) (h2 : 24 * u < 24 * M) :
    (3 * u) / M = 2 := by
  omega
