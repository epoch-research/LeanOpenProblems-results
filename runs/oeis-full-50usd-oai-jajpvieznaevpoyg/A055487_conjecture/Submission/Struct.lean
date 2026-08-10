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

lemma prime_factor_sub_one_dvd_of_totient_eq {m r N : ℕ} (hm : m ≠ 0)
    (hphi : Nat.totient m = N) (hrm : r ∈ m.primeFactors) : r - 1 ∣ N := by
  rw [← hphi]
  exact prime_factor_sub_one_dvd_totient hm hrm
