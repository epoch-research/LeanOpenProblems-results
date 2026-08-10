import FormalConjectures.Util.ProblemImports
lemma test_pow1 (k : ℕ) (hk_ge : k ≥ 1) : 4 ∣ 2^(2 * (2 * k)) := by
  have : 2^(2 * (2 * k)) = 4^(2 * k) := by
    rw [show 2^(2 * (2 * k)) = (2^2)^(2 * k) by rw [← pow_mul, mul_comm]]
    rfl
  rw [this]
  use 4^(2 * k - 1)
  have : 2 * k = (2 * k - 1) + 1 := by omega
  nth_rw 1 [this]
  rw [pow_add]
  ring
lemma test_pow2 (k : ℕ) (hk_ge : k ≥ 1) : 4 ∣ 2^(2 * k) := by
  have : 2^(2 * k) = 4^k := by
    rw [show 2^(2 * k) = (2^2)^k by rw [← pow_mul, mul_comm]]
    rfl
  rw [this]
  use 4^(k - 1)
  have : k = (k - 1) + 1 := by omega
  nth_rw 1 [this]
  rw [pow_add]
  ring
