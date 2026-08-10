import FormalConjectures.Util.ProblemImports

example (p n : ℕ) (hp : Nat.Prime p) (hnp : n < p) (hple : p ≤ (3*n - 1)/2) :
    p ^ 3 ∣ Nat.choose (3*n) n * (Nat.choose (2*n) n)^2 := by
  have h2p : 2*p ≤ 3*n - 1 := by omega
  have h2p' : 2*p < 3*n := by omega
  have hp2n : p ≤ 2*n := by omega
  have h3n_lt : 3*n < p^2 := by nlinarith [hnp, hp.two_le]
  have h2n_lt : 2*n < p^2 := by nlinarith [hnp, hp.two_le]
  -- Use prime.pow_dvd_iff_le_factorization
  rw [hp.pow_dvd_iff_le_factorization]
  rw [Nat.factorization_mul]
  · rw [Nat.factorization_pow]
    -- need choose factors nonzero, then factorization_choose formulas maybe
    sorry
  · exact Nat.choose_ne_zero (by omega)
  · exact pow_ne_zero 2 (Nat.choose_ne_zero (by omega))
