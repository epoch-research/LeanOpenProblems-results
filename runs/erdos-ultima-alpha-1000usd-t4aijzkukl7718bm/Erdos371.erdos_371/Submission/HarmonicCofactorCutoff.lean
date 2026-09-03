import Submission.MediumPrimeSieve

/-! A cofactor cutoff specified by a quantile of the prime harmonic sum.
The second-moment sieve controls integers avoiding the intervening primes. -/

namespace Erdos371

noncomputable def primeHarmonic (B : ℕ) : ℝ := primeReciprocalSum (B + 1).primesBelow

lemma primeHarmonic_nonneg (B : ℕ) : 0 ≤ primeHarmonic B := primeReciprocalSum_nonneg _

@[simp] lemma primeHarmonic_zero : primeHarmonic 0 = 0 := by
  norm_num [primeHarmonic, primeReciprocalSum, Nat.primesBelow, Finset.sum_filter]

open Filter in
lemma primeHarmonic_atTop : Tendsto primeHarmonic atTop atTop := by
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => Set.indicator_nonneg (fun p _ => by positivity) n)).mp not_summable_one_div_on_primes
  change Tendsto (fun B : ℕ => ∑ p ∈ (B + 1).primesBelow, (1 : ℝ) / (p : ℝ)) atTop atTop
  simpa [Nat.primesBelow, Finset.sum_filter, Set.indicator, Function.comp_def] using
    ht.comp (tendsto_add_atTop_nat 1)

/-- Largest cutoff at which at most half of the available prime reciprocal
mass has accumulated. This is a function of B alone. -/
noncomputable def harmonicCofactorCutoff (B : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun K => primeHarmonic K ≤ primeHarmonic B / 2) B

lemma harmonicCofactorCutoff_le (B : ℕ) : harmonicCofactorCutoff B ≤ B :=
  Nat.findGreatest_le B

lemma harmonicCofactorCutoff_mass_le (B : ℕ) :
    primeHarmonic (harmonicCofactorCutoff B) ≤ primeHarmonic B / 2 := by
  classical
  exact Nat.findGreatest_spec (P := fun K => primeHarmonic K ≤ primeHarmonic B / 2)
    (Nat.zero_le B) (by
    dsimp only
    rw [primeHarmonic_zero]
    exact div_nonneg (primeHarmonic_nonneg B) (by norm_num))

open Filter in
lemma harmonicCofactorCutoff_atTop : Tendsto harmonicCofactorCutoff atTop atTop := by
  classical
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [eventually_ge_atTop K,
    primeHarmonic_atTop.eventually_ge_atTop (2 * primeHarmonic K)] with B hBK hBH
  apply Nat.le_findGreatest hBK
  linarith

def mediumPrimes (K B : ℕ) : Finset ℕ := (B + 1).primesBelow \ (K + 1).primesBelow

lemma mem_mediumPrimes {K B p : ℕ} : p ∈ mediumPrimes K B ↔ p.Prime ∧ K < p ∧ p ≤ B := by
  by_cases hp : p.Prime <;> simp [mediumPrimes, Nat.mem_primesBelow, hp] <;> omega

lemma mediumPrimes_sum (K B : ℕ) (hKB : K ≤ B) :
    primeReciprocalSum (mediumPrimes K B) + primeHarmonic K = primeHarmonic B := by
  apply Finset.sum_sdiff
  exact Finset.filter_subset_filter _ (Finset.range_mono (by omega))

lemma harmonicCofactorCutoff_remaining_mass (B : ℕ) :
    primeHarmonic B / 2 ≤ primeReciprocalSum (mediumPrimes (harmonicCofactorCutoff B) B) := by
  have h₁ := harmonicCofactorCutoff_mass_le B
  have h₂ := mediumPrimes_sum (harmonicCofactorCutoff B) B (harmonicCofactorCutoff_le B)
  linarith

open Filter in
lemma harmonicCofactorCutoff_remaining_mass_atTop :
    Tendsto (fun B => primeReciprocalSum (mediumPrimes (harmonicCofactorCutoff B) B)) atTop atTop :=
  tendsto_atTop_mono harmonicCofactorCutoff_remaining_mass
    (Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) primeHarmonic_atTop)

lemma mediumPrimes_card_le (K B : ℕ) : (mediumPrimes K B).card ≤ B + 1 := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    ((Finset.card_filter_le _ _).trans_eq (Finset.card_range (B + 1)))

lemma primeAvoidCount_succ_le (S : Finset ℕ) (N : ℕ) :
    primeAvoidCount S (N + 1) ≤ primeAvoidCount S N + 1 := by
  unfold primeAvoidCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

open Filter in
/-- A growing harmonic-quantile cutoff gives a negligible exceptional set.
Unlike the previous bound, there is no factor K in the error. -/
theorem harmonicCofactorCutoff_avoid_count_tendsto (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) (hBN : ∀ᶠ N in atTop, B N ≤ N) :
    Tendsto (fun N =>
      (primeAvoidCount (mediumPrimes (harmonicCofactorCutoff (B N)) (B N)) N : ℝ) / N)
      atTop (nhds 0) := by
  have hH := harmonicCofactorCutoff_remaining_mass_atTop.comp hB
  have ht := (tendsto_inv_atTop_zero.comp hH).const_mul (5 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hBN, hH.eventually_gt_atTop 0, eventually_gt_atTop 0] with N hBN hHN hN
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [div_eq_mul_inv] using primeAvoidCount_ratio_le
    (mediumPrimes (harmonicCofactorCutoff (B N)) (B N)) N
      (fun p hp => (mem_mediumPrimes.mp hp).1)
      ((mediumPrimes_card_le _ _).trans (by omega)) hN hHN

open Filter in
theorem harmonicCofactorCutoff_avoid_count_succ_tendsto (B : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) (hBN : ∀ᶠ N in atTop, B N ≤ N) :
    Tendsto (fun N =>
      (primeAvoidCount (mediumPrimes (harmonicCofactorCutoff (B N)) (B N)) (N + 1) : ℝ) / N)
      atTop (nhds 0) := by
  have ht := (harmonicCofactorCutoff_avoid_count_tendsto B hB hBN).add
    tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  rw [← add_div]
  have hc := primeAvoidCount_succ_le (mediumPrimes (harmonicCofactorCutoff (B N)) (B N)) N
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg N)

open Filter in
lemma subpower_cutoff_eventually_le (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    ∀ᶠ N in atTop, B N ≤ N := by
  filter_upwards [(tendsto_order.mp hB).2 1 (by norm_num), eventually_gt_atTop 1] with N hBN hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlog : Real.log (B N + 1 : ℝ) ≤ Real.log N := by
    have h := (div_le_iff₀ hlogN).mp hBN.le
    simpa only [one_mul] using h
  have hc : (B N + 1 : ℝ) ≤ N := (Real.log_le_log_iff (by positivity) hN0).mp hlog
  have hn : B N + 1 ≤ N := by exact_mod_cast hc
  omega

#print axioms primeHarmonic_atTop
#print axioms harmonicCofactorCutoff_atTop
#print axioms harmonicCofactorCutoff_remaining_mass_atTop
#print axioms harmonicCofactorCutoff_avoid_count_succ_tendsto
end Erdos371
