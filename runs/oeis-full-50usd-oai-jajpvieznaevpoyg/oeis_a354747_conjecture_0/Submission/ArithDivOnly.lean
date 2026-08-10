import FormalConjectures.Util.ProblemImports

namespace ArithDivOnly

def M : ℕ := 2 * 100943 * 3 ^ 39101
lemma dvd_div_of_mul_eq_of_prime_dvd_cofactor {d c q M : ℕ}
    (hqpos : 0 < q) (hM : M = d * c) (hqc : q ∣ c) : d ∣ M / q := by
  rcases hqc with ⟨c', hc'⟩
  subst c
  refine ⟨c', ?_⟩
  rw [hM]
  have hcomm : d * (q * c') = q * (d * c') := by ring
  rw [hcomm, Nat.mul_div_cancel_left _ hqpos]

end ArithDivOnly
