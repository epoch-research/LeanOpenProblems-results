import Submission.OddCharacterSkew

/-!
Aligning the two hyperbolic endpoints costs at most one in the upper-half
prime-band discrepancy. This permits a global odd-character formula with a
uniformly bounded error. The remaining character sum is not estimated here.
-/

namespace Erdos371
open Finset

lemma bilinearCount_succ (N p q : ℕ) :
    bilinearCount (N + 1) p q = bilinearCount N p q +
      if p ∣ N + 1 ∧ q ∣ N + 2 then 1 else 0 := by
  unfold bilinearCount
  rw [range_add_one, filter_insert]
  by_cases h : p ∣ N + 1 ∧ q ∣ N + 2
  · rw [if_pos h, if_pos h, card_insert_of_notMem]
    simp
  · simp [h]

lemma cofactorResidueCount_endpoint (N p q : ℕ) (hq : 2 ≤ q) :
    cofactorResidueCount (N + 1) p q true = cofactorResidueCount N p q true +
      if p ∣ N ∧ q ∣ N + 1 then 1 else 0 := by
  cases N with
  | zero =>
      have hq₁ : ¬ q ∣ 1 := by simp only [Nat.dvd_one]; omega
      have hdiv : 1 / q = 0 := Nat.div_eq_of_lt (by omega)
      simp [cofactorResidueCount, hq₁, hdiv]
  | succ N =>
      rw [← bilinearCount_cofactor_positive (N + 1) p q hq,
        ← bilinearCount_cofactor_positive N p q hq, bilinearCount_succ]

noncomputable def commonEndpointPrimeSkew (B C N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C),
    ∑ b ∈ Icc 1 (N / (C + 1)),
      ((oppositePrimeCount C (N / b) p b true : ℝ) - oppositePrimeCount C (N / b) p b false)

noncomputable def primeBandEndpoint (B C N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C),
    ∑ q ∈ (range (N + 2)).filter (fun q => q.Prime ∧ C < q),
      if p ∣ N ∧ q ∣ N + 1 then 1 else 0

/-- Both signs on the right now have the same prime endpoint `N / b`.
The correction is the single integer endpoint, not an error per modulus. -/
theorem primeBandDiscrepancy_common_endpoint (B C N : ℕ) :
    primeBandDiscrepancy B C N = commonEndpointPrimeSkew B C N + primeBandEndpoint B C N := by
  unfold primeBandDiscrepancy commonEndpointPrimeSkew primeBandEndpoint
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hrow :
      (∑ q ∈ (range (N + 2)).filter (fun q => q.Prime ∧ C < q),
        ((cofactorResidueCount N p q true : ℝ) - cofactorResidueCount N p q false)) =
      ∑ b ∈ Icc 1 (N / (C + 1)),
        ((oppositePrimeCount C (N / b) p b true : ℝ) - oppositePrimeCount C (N / b) p b false) := by
    rw [sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum,
      sum_cofactorResidueCount N C N p true (by omega),
      sum_cofactorResidueCount N C N p false (by omega)]
    simp only [Nat.cast_sum, sum_sub_distrib]
  rw [← hrow, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hqp := (mem_filter.mp hq).2.1
  rw [bilinearCount_cofactor_positive N p q hqp.two_le,
    bilinearCount_cofactor_negative N p q hqp.pos,
    cofactorResidueCount_endpoint N p q hqp.two_le, Nat.cast_add]
  split_ifs <;> norm_num <;> ring

lemma prime_dvd_unique_above_sqrt (B n p q : ℕ) (hn : 0 < n) (hsize : n ≤ B^2)
    (hp : p.Prime) (hq : q.Prime) (hBp : B < p) (hBq : B < q)
    (hpn : p ∣ n) (hqn : q ∣ n) : p = q := by
  by_contra hne
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro h
    have he := (hq.dvd_iff_eq hp.ne_one).mp h
    exact hne he.symm)
  have hprod := Nat.le_of_dvd hn (hc.mul_dvd_of_dvd_of_dvd hpn hqn)
  have hmin : (B + 1) * (B + 1) ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

private lemma large_prime_divisor_card_le_one (S : Finset ℕ) (B n : ℕ)
    (hn : 0 < n) (hsize : n ≤ B^2) (hS : ∀ p ∈ S, p.Prime ∧ B < p) :
    (S.filter fun p => p ∣ n).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpS, hpn⟩ := mem_filter.mp hp
  obtain ⟨hqS, hqn⟩ := mem_filter.mp hq
  exact prime_dvd_unique_above_sqrt B n p q hn hsize
    (hS p hpS).1 (hS q hqS).1 (hS p hpS).2 (hS q hqS).2 hpn hqn

lemma primeBandEndpoint_bounds (B C N : ℕ) (hBC : B ≤ C) (hsize : N + 1 ≤ B^2) :
    0 ≤ primeBandEndpoint B C N ∧ primeBandEndpoint B C N ≤ 1 := by
  have heq : primeBandEndpoint B C N =
      (((range (N + 2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C)).filter (fun p => p ∣ N)).card *
      ((((range (N + 2)).filter (fun q => q.Prime ∧ C < q)).filter (fun q => q ∣ N + 1)).card : ℝ) := by
    unfold primeBandEndpoint
    rw [← sum_boole, ← sum_boole, sum_mul_sum]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    split_ifs <;> norm_num <;> tauto
  constructor
  · unfold primeBandEndpoint
    apply sum_nonneg
    intro p hp
    apply sum_nonneg
    intro q hq
    split_ifs <;> norm_num
  · cases N with
    | zero =>
        unfold primeBandEndpoint
        have hq (q : ℕ) (hq : q ∈ (range 2).filter (fun q => q.Prime ∧ C < q)) : ¬ q ∣ 1 :=
          (mem_filter.mp hq).2.1.not_dvd_one
        apply le_trans (le_of_eq (sum_eq_zero (fun p hp => sum_eq_zero (fun q hq' => by simp [hq q hq']))))
        norm_num
    | succ N =>
        rw [heq]
        have hp := large_prime_divisor_card_le_one
          ((range (N + 1 + 2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C)) B (N + 1)
          (by omega) (by omega) (by
            intro p hp
            obtain ⟨_, hp, hBp, _⟩ := mem_filter.mp hp
            exact ⟨hp, hBp⟩)
        have hq := large_prime_divisor_card_le_one
          ((range (N + 1 + 2)).filter (fun q => q.Prime ∧ C < q)) B (N + 1 + 1)
          (by omega) hsize (by
            intro q hq
            obtain ⟨_, hq, hCq⟩ := mem_filter.mp hq
            exact ⟨hq, by omega⟩)
        have hp' : (((range (N + 1 + 2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C)).filter
            (fun p => p ∣ N + 1)).card ≤ (1 : ℝ) := by exact_mod_cast hp
        have hq' : (((range (N + 1 + 2)).filter (fun q => q.Prime ∧ C < q)).filter
            (fun q => q ∣ N + 1 + 1)).card ≤ (1 : ℝ) := by exact_mod_cast hq
        exact mul_le_one₀ hp' (Nat.cast_nonneg _) hq'

/-- Aligning the hyperbolic endpoints costs at most one in total. -/
theorem primeBandDiscrepancy_common_endpoint_bound (B C N : ℕ)
    (hBC : B ≤ C) (hsize : N + 1 ≤ B^2) :
    |primeBandDiscrepancy B C N - commonEndpointPrimeSkew B C N| ≤ 1 := by
  rw [primeBandDiscrepancy_common_endpoint]
  have h := primeBandEndpoint_bounds B C N hBC hsize
  simpa only [add_sub_cancel_left, abs_of_nonneg h.1] using h.2

/-- The common-endpoint hyperbolic sum has only odd characters. The
prime endpoint still depends on the cofactor `b`; no rectangular replacement
has been made. -/
lemma hyperbolicOppositePrime_odd_characters (C N p : ℕ) [NeZero p] :
    (p.totient : ℂ) *
      (∑ b ∈ Icc 1 (N / (C + 1)),
        ((oppositePrimeCount C (N / b) p b true : ℂ) - oppositePrimeCount C (N / b) p b false)) =
      2 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
        ∑ b ∈ Icc 1 (N / (C + 1)),
          χ (b : ZMod p) * ∑ q ∈ (Ioc C (N / b)).filter Nat.Prime, χ (q : ZMod p) := by
  classical
  rw [mul_sum]
  calc
    _ = ∑ b ∈ Icc 1 (N / (C + 1)),
        2 * ∑ χ : DirichletCharacter ℂ p, if χ.Odd then
          χ (b : ZMod p) * ∑ q ∈ (Ioc C (N / b)).filter Nat.Prime, χ (q : ZMod p) else 0 := by
      apply sum_congr rfl
      intro b hb
      exact oppositePrimeCount_odd_characters C (N / b) p b (mem_Icc.mp hb).1
    _ = _ := by
      simp_rw [← sum_filter, ← mul_sum]
      rw [sum_comm]

noncomputable def oddHyperbolicPrimeSkew (B C N : ℕ) : ℂ :=
  ∑ p ∈ (range (N + 2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C),
    (2 / (p.totient : ℂ)) *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
        ∑ b ∈ Icc 1 (N / (C + 1)),
          χ (b : ZMod p) * ∑ q ∈ (Ioc C (N / b)).filter Nat.Prime, χ (q : ZMod p)

lemma commonEndpointPrimeSkew_characters (B C N : ℕ) :
    (commonEndpointPrimeSkew B C N : ℂ) = oddHyperbolicPrimeSkew B C N := by
  classical
  unfold commonEndpointPrimeSkew oddHyperbolicPrimeSkew
  push_cast
  apply sum_congr rfl
  intro p hp
  have hpp := (mem_filter.mp hp).2.1
  letI : NeZero p := ⟨hpp.ne_zero⟩
  have hφ : (p.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hpp.pos).ne'
  apply mul_left_cancel₀ hφ
  rw [hyperbolicOppositePrime_odd_characters, ← mul_assoc, mul_div_cancel₀ _ hφ]

/-- The global hyperbolic odd-character sum approximates the original
prime-band discrepancy with error at most one. This is an exact arithmetic
reduction, not an estimate of the character sum itself. -/
theorem primeBandDiscrepancy_odd_hyperbola_bound (B C N : ℕ)
    (hBC : B ≤ C) (hsize : N + 1 ≤ B^2) :
    ‖(primeBandDiscrepancy B C N : ℂ) - oddHyperbolicPrimeSkew B C N‖ ≤ 1 := by
  rw [← commonEndpointPrimeSkew_characters, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact primeBandDiscrepancy_common_endpoint_bound B C N hBC hsize

lemma primeBandEndpoint_eq_zero_of_max_le (B C N : ℕ)
    (hC : Nat.maxPrimeFac (N + 1) ≤ C) : primeBandEndpoint B C N = 0 := by
  unfold primeBandEndpoint
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro q hq
  have hqp := (mem_filter.mp hq).2.1
  have hCq := (mem_filter.mp hq).2.2
  have hnd : ¬ q ∣ N + 1 := by
    intro hd
    have hle := Nat.le_maxPrimeFac (by omega : N + 1 ≠ 0) hqp hd
    omega
  simp [hnd]

lemma smoothSkew_common_endpoint_correction_bounds (B C N : ℕ)
    (hBC : B ≤ C) (hsize : N + 1 ≤ B^2) :
    0 ≤ smoothIndicator C (N + 1) - smoothIndicator B (N + 1) + primeBandEndpoint B C N ∧
      smoothIndicator C (N + 1) - smoothIndicator B (N + 1) + primeBandEndpoint B C N ≤ 1 := by
  by_cases hC : Nat.maxPrimeFac (N + 1) ≤ C
  · rw [primeBandEndpoint_eq_zero_of_max_le B C N hC]
    simp only [smoothIndicator, if_pos hC, add_zero]
    split_ifs <;> norm_num
  · have hB : ¬ Nat.maxPrimeFac (N + 1) ≤ B := by omega
    simpa only [smoothIndicator, if_neg hC, if_neg hB, sub_self, zero_add] using
      primeBandEndpoint_bounds B C N hBC hsize

/-- The two endpoint corrections are mutually exclusive, so even the full
smooth-cutoff skew differs from the odd-character hyperbola by at most one. -/
theorem smoothCutoffSkew_odd_hyperbola_bound (B C N : ℕ)
    (hB : 1 ≤ B) (hBC : B ≤ C) (hsize : N + 1 ≤ B^2) :
    ‖(smoothCutoffSkew B C N : ℂ) - oddHyperbolicPrimeSkew B C N‖ ≤ 1 := by
  rw [← commonEndpointPrimeSkew_characters, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  rw [smoothCutoffSkew_above_sqrt B C N hB hBC hsize,
    primeBandDiscrepancy_common_endpoint]
  have h := smoothSkew_common_endpoint_correction_bounds B C N hBC hsize
  have he : smoothIndicator C (N + 1) - smoothIndicator B (N + 1) +
      (commonEndpointPrimeSkew B C N + primeBandEndpoint B C N) - commonEndpointPrimeSkew B C N =
      smoothIndicator C (N + 1) - smoothIndicator B (N + 1) + primeBandEndpoint B C N := by ring
  rw [he, abs_of_nonneg h.1]
  exact h.2

#print axioms primeBandDiscrepancy_common_endpoint
#print axioms primeBandEndpoint_bounds
#print axioms primeBandDiscrepancy_common_endpoint_bound
#print axioms commonEndpointPrimeSkew_characters
#print axioms primeBandDiscrepancy_odd_hyperbola_bound
#print axioms smoothCutoffSkew_odd_hyperbola_bound

end Erdos371
