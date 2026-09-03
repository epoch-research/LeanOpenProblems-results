import FormalConjecturesUtil

/-! An obstruction to extending the cubic construction by polynomial identities. -/


namespace Erdos322Research

/-- Over the reals, a constant sum of positive even powers of polynomials forces
all the polynomials to be constant. -/
theorem constant_of_even_power_sum {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℝ) (k : ℕ) (hk : Even k) (hkpos : 0 < k)
    (n : ℝ) (h : ∀ x : ℝ, ∑ i, (p i).eval x ^ k = n) :
    ∀ i, p i = Polynomial.C ((p i).coeff 0) := by
  classical
  intro i
  apply Polynomial.eq_C_of_degree_le_zero
  apply (Polynomial.abs_isBoundedUnder_iff (p i)).mp
  refine ⟨max 1 n, Filter.eventually_map.mpr (Filter.Eventually.of_forall ?_)⟩
  intro x
  have hp : |(p i).eval x| ^ k ≤ n := by
    rw [hk.pow_abs]
    rw [← h x]
    exact Finset.single_le_sum (f := fun j ↦ (p j).eval x ^ k)
      (fun j _ ↦ hk.pow_nonneg _) (Finset.mem_univ i)
  by_cases hsmall : |(p i).eval x| ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  · have hlarge : 1 ≤ |(p i).eval x| := le_of_not_ge hsmall
    exact ((le_self_pow₀ hlarge hkpos.ne').trans hp).trans (le_max_right _ _)

end Erdos322Research
