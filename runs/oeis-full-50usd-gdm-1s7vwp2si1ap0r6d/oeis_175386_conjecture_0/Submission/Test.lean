
lemma exists_prime_in_interval (n : ℕ) (hn : 2 ≤ n) :
    ∃ p, Nat.Prime p ∧ n / 2 < p ∧ p ≤ n := by
  have h_ex := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  obtain ⟨p, hp, h1, h2⟩ := h_ex
  refine ⟨p, hp, h1, ?_⟩
  have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  omega
