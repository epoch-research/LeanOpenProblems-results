import Submission.Spec

/-! A uniform divisor bound on the constructed quartic subfamily.
This is not an upper bound on all quartic representations. -/

namespace Erdos322.QuarticSuperlog

lemma parameter_count_le_divisor_count {r m : ℕ} (q : Fin r → ℕ)
    (hq : ∀ i, 1 < q i) (hqq : Pairwise (Function.onFun Nat.Coprime q)) :
    (m + 1) ^ r ≤ ((∏ i, q i) ^ m).divisors.card := by
  classical
  have hpos : 0 < ∏ i, q i := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have h := Finset.card_le_card_of_injOn
    (fun j : Fin r → Fin (m + 1) ↦ ∏ i, q i ^ (j i : ℕ))
    (s := Finset.univ) (t := ((∏ i, q i) ^ m).divisors)
    (by
      intro j _
      apply Nat.mem_divisors.mpr
      refine ⟨?_, (pow_pos hpos m).ne'⟩
      rw [← Finset.prod_pow]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦
        Nat.pow_dvd_pow _ (Nat.le_of_lt_succ (j i).isLt))
    (coprime_power_product_injective q hq hqq).injOn
  simpa using h

/-- The number of representations supplied by the construction is uniformly
subpolynomial in its target, even when the number of norm factors varies. -/
theorem constructed_family_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (r m : ℕ) (q : Fin r → ℕ),
      (∀ i, 1 < q i) → Pairwise (Function.onFun Nat.Coprime q) →
      ((m + 1 : ℕ) : ℝ) ^ r ≤ C * ((2 * (∏ i, q i) ^ (4 * m) + 1 : ℕ) : ℝ) ^ ε := by
  obtain ⟨C,hC,hdiv⟩ := Erdos322.divisor_count_subpolynomial ε hε
  refine ⟨C,hC,fun r m q hq hqq ↦ ?_⟩
  have hB : 0 < ∏ i, q i := Finset.prod_pos fun i _ ↦ by have := hq i; omega
  have hpow : 0 < (∏ i, q i) ^ m := pow_pos hB _
  have hle : (∏ i, q i) ^ m ≤ 2 * (∏ i, q i) ^ (4 * m) + 1 := by
    have h := Nat.pow_le_pow_right hB (show m ≤ 4 * m by omega)
    omega
  calc
    ((m + 1 : ℕ) : ℝ) ^ r ≤ (((∏ i, q i) ^ m).divisors.card : ℝ) := by
      exact_mod_cast parameter_count_le_divisor_count q hq hqq
    _ ≤ C * (((∏ i, q i) ^ m : ℕ) : ℝ) ^ ε := hdiv _ hpow
    _ ≤ C * ((2 * (∏ i, q i) ^ (4 * m) + 1 : ℕ) : ℝ) ^ ε := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) hε.le

end Erdos322.QuarticSuperlog

#print axioms Erdos322.QuarticSuperlog.parameter_count_le_divisor_count
#print axioms Erdos322.QuarticSuperlog.constructed_family_uniform_bound
