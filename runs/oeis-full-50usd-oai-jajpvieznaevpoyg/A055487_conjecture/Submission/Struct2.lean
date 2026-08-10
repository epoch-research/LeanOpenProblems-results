import FormalConjectures.Util.ProblemImports
open Set
open Nat

lemma prime_factor_sub_one_dvd_totient {m r : ℕ} (hm : m ≠ 0) (hrm : r ∈ m.primeFactors) :
    r - 1 ∣ Nat.totient m := by
  rw [Nat.totient_eq_prod_factorization hm]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  exact (Nat.dvd_mul_left (r - 1) (r ^ (m.factorization r - 1))).trans
    (Finset.dvd_prod_of_mem (s := m.primeFactors)
      (f := fun p => p ^ (m.factorization p - 1) * (p - 1)) hrm)

lemma prime_factor_sub_one_dvd_of_totient_eq_factorial {m r n : ℕ} (hm : m ≠ 0)
    (hphi : Nat.totient m = Nat.factorial n) (hrm : r ∈ m.primeFactors) :
    r - 1 ∣ Nat.factorial n := by
  rw [← hphi]
  exact prime_factor_sub_one_dvd_totient hm hrm

lemma prime_factor_exp_eq_one_of_totient_factorial_of_lt {m r n : ℕ} (hm : m ≠ 0)
    (hphi : Nat.totient m = Nat.factorial n) (hrm : r ∈ m.primeFactors) (hnr : n < r) :
    m.factorization r = 1 := by
  have hr : Nat.Prime r := Nat.prime_of_mem_primeFactors hrm
  have hposfac : 0 < m.factorization r := by
    exact hr.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hrm)
  have hle : m.factorization r ≤ 1 := by
    by_contra hnot
    have h2 : 2 ≤ m.factorization r := by omega
    have hrdvdphi : r ∣ Nat.totient m := by
      rw [Nat.totient_eq_prod_factorization hm]
      rw [Nat.prod_factorization_eq_prod_primeFactors]
      have hpow : r ∣ r ^ (m.factorization r - 1) * (r - 1) := by
        have hpos : 0 < m.factorization r - 1 := by omega
        exact dvd_mul_of_dvd_left (dvd_pow_self r hpos.ne') _
      exact hpow.trans (Finset.dvd_prod_of_mem (s := m.primeFactors)
        (f := fun p => p ^ (m.factorization p - 1) * (p - 1)) hrm)
    have hrdvdfact : r ∣ Nat.factorial n := by simpa [hphi] using hrdvdphi
    exact (not_le_of_gt hnr) (hr.dvd_factorial.mp hrdvdfact)
  omega
