import FormalConjectures.Util.ProblemImports
open Nat
#check Nat.factorization_eq_zero_iff
#check Nat.factorization_eq_zero_of_not_prime
#check Nat.Prime.dvd_iff_one_le_factorization
example {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 12.factorization p = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  intro hd
  have hp12 := hp.eq_two_or_odd
  -- try norm_num at hd?
  interval_cases p <;> simp_all
