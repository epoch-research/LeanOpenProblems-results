import FormalConjectures.Util.ProblemImports

lemma dvd_div_of_mul_eq_of_prime_dvd_cofactor {d c q M : ℕ}
    (hqpos : 0 < q) (hM : M = d * c) (hqc : q ∣ c) : d ∣ M / q := by
  rcases hqc with ⟨c', hc'⟩
  subst c
  refine ⟨c', ?_⟩
  rw [hM]
  have hcomm : d * (q * c') = q * (d * c') := by ring
  rw [hcomm, Nat.mul_div_cancel_left _ hqpos]

lemma divisor_eq_M_abs {M d : ℕ}
    (hclass : ∀ {r : ℕ}, Nat.Prime r → r ∣ M → r = 2 ∨ r = 3 ∨ r = 100943)
    (hd : d ∣ M)
    (h2 : ¬ d ∣ M / 2) (h3 : ¬ d ∣ M / 3) (h100943 : ¬ d ∣ M / 100943) : d = M := by
  rcases hd with ⟨c, hM'⟩
  have hM : M = d * c := hM'
  have hc1 : c = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro r hrp hrc
    have hrM : r ∣ M := by
      rw [hM]
      exact dvd_mul_of_dvd_right hrc d
    rcases hclass hrp hrM with rfl | rfl | rfl
    · exact h2 (dvd_div_of_mul_eq_of_prime_dvd_cofactor (by norm_num) hM hrc)
    · exact h3 (dvd_div_of_mul_eq_of_prime_dvd_cofactor (by norm_num) hM hrc)
    · exact h100943 (dvd_div_of_mul_eq_of_prime_dvd_cofactor (by norm_num) hM hrc)
  rw [hM, hc1, mul_one]
