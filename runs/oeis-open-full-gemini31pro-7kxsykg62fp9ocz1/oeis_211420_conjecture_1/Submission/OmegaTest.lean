import Mathlib

lemma div_ineq (N R M : ℕ) (h : 0 < M) :
    (4 * N - R) / M + (3 * N) / M + (2 * N) / M ≤ (8 * N - 2 * R) / M + (8 * R) / M + N / M := by
  omega
