import Mathlib

lemma no_sum_sq_of_padic (R q k M : ℕ)
    (hR0 : R ≠ 0)
    (hq_prime : q.Prime)
    (hR : R = q ^ (2 * k + 1) * M)
    (hM : ¬ q ∣ M)
    (hq3 : q % 4 = 3) :
    ∀ a b : ℕ, a ^ 2 + b ^ 2 ≠ R := by
  intro a b hab
  have h_eq : ∃ x y, R = x ^ 2 + y ^ 2 := ⟨a, b, hab.symm⟩
  have h_iff := Nat.eq_sq_add_sq_iff.mp h_eq q
  have h_mem : q ∈ R.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hq_prime, hR0, ?_⟩
    rw [hR]
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  have h_even := h_iff h_mem hq3
  have h_padic : padicValNat q R = 2 * k + 1 := by
    rw [hR]
    rw [padicValNat.mul hq_prime (pow_ne_zero _ hq_prime.ne_zero) (by rintro rfl; exact hM (dvd_zero _))]
    have : padicValNat q M = 0 := padicValNat.eq_zero_of_not_dvd hM
    rw [this, add_zero]
    exact padicValNat.pow hq_prime _
  rw [h_padic] at h_even
  revert h_even
  simp [Even]
