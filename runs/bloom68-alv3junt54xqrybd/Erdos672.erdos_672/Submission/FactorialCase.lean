import Submission.ArithmeticProgressions

/-! The progression starting at one with step one has a nonpower product.
This is a special case, not the full arithmetic-progression conjecture. -/

namespace Erdos672.Progression

/-- Bertrand's prime has valuation one in the factorial. -/
theorem factorial_ne_nontrivial_power (k l q : ℕ)
    (hk : 4 ≤ k) (hl : 1 < l) : k.factorial ≠ q ^ l := by
  obtain ⟨p, hp, hlow, hupp⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
  have hpk : p ≤ k := hupp.trans (Nat.mul_div_le k 2)
  have hrem : k - p < p := by omega
  letI : Fact p.Prime := ⟨hp⟩
  have hv : k.factorial.factorization p = 1 := by
    rw [Nat.factorization_def _ hp]
    have hrepr : k = p * 1 + (k - p) := by omega
    rw [hrepr, padicValNat_factorial_mul_add 1 hrem, padicValNat_factorial_mul 1]
    simp
  intro hpower
  have heq := congrArg (fun x : ℕ => x.factorization p) hpower
  change k.factorial.factorization p = (q ^ l).factorization p at heq
  rw [hv, Nat.factorization_pow] at heq
  simp only [Finsupp.smul_apply, smul_eq_mul] at heq
  have hdiv : l ∣ 1 := ⟨q.factorization p, heq⟩
  have : l = 1 := Nat.dvd_one.mp hdiv
  omega

/-- The `n = d = 1` progression case, uniformly over lengths and exponents. -/
theorem range_one_step_one_ne_power (k l q : ℕ)
    (hk : 4 ≤ k) (hl : 1 < l) :
    (∏ i ∈ Finset.range k, (1 + i * 1)) ≠ q ^ l := by
  have hprod : (∏ i ∈ Finset.range k, (1 + i * 1)) = k.factorial := by
    simpa only [Nat.mul_one, Nat.add_comm] using Finset.prod_range_add_one_eq_factorial k
  rw [hprod]
  exact factorial_ne_nontrivial_power k l q hk hl

end Erdos672.Progression
