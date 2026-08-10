import Mathlib.Data.Nat.GCD.Basic

lemma test_cop_dvd (n a M_small : ℕ) (h_cop : Nat.Coprime n 10) (hdvd : n ∣ 10 ^ a * M_small) : n ∣ M_small := by
  have h_cop_pow : Nat.Coprime n (10 ^ a) := by
    have h := Nat.Coprime.pow 1 a h_cop
    simp only [pow_one] at h
    exact h
  exact Nat.Coprime.dvd_of_dvd_mul_left h_cop_pow hdvd
