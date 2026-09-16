import Mathlib

lemma test (u M : ℕ) (hM : 0 < M) (h1 : 16 * M ≤ 24 * u) (h2 : 24 * u < 24 * M) :
    (3 * u) / M = 2 := by
  have H : 3 * u = 2 * M + (3 * u - 2 * M) := by omega
  have H2 : 3 * u - 2 * M < M := by omega
  -- actually we can just use Nat.div_eq_of_lt_le
  sorry
