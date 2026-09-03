import Submission.RoughMobiusHarmonic

/-! Uniform endpoint continuity of ONE-coordinate largest-prime marginals.
Alladi duality turns the rounding error into a rough-number count. No
adjacent pair observable is covered by this argument. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def primeMarginalMean (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, g (Nat.maxPrimeFac (n+1)))/(N : ℝ)

lemma summatory_divisor_sum_eq_extended_floor_sum (f : ℕ → ℝ) (N X : ℕ) (hNX : N ≤ X) :
    (∑ n ∈ range N, ∑ d ∈ (n+1).divisors, f d) =
      ∑ d ∈ range (X+1), f d*((N/d : ℕ) : ℝ) := by
  calc
    _ = ∑ n ∈ range N, ∑ d ∈ range (X+1), if d ∣ n+1 then f d else 0 := by
      apply sum_congr rfl
      intro n hn
      exact sum_divisors_eq_range (n+1) (X+1) (by omega)
        (by have := mem_range.mp hn; omega) f
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [← sum_filter]
      simp [Nat.card_multiples,mul_comm]

lemma alladi_divisors_of_value_one_zero (g : ℕ → ℝ) (hg : g 1=0) (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, leastFactorTerm g d) = -g (Nat.maxPrimeFac n) := by
  by_cases h : n=1
  · subst n
    simp [leastFactorTerm,hg]
  · exact alladi_divisors n (by omega) g

lemma primeMarginalMean_floor_sum (g : ℕ → ℝ) (hg : g 1=0)
    (N X : ℕ) (hNX : N ≤ X) :
    primeMarginalMean g N =
      -(∑ d ∈ range (X+1), leastFactorTerm g d*((N/d : ℕ) : ℝ))/(N : ℝ) := by
  unfold primeMarginalMean
  rw [← summatory_divisor_sum_eq_extended_floor_sum _ N X hNX]
  simp_rw [alladi_divisors_of_value_one_zero g hg _ (Nat.zero_lt_succ _)]
  rw [sum_neg_distrib,neg_neg]

lemma leastFactorTerm_rough_bound (g : ℕ → ℝ) (B d : ℕ)
    (hg : ∀ p, |g p| ≤ 1) (hzero : ∀ p, p ≤ B → g p=0) :
    |leastFactorTerm g d| ≤ if 1 < d ∧ B < d.minFac then (1 : ℝ) else 0 := by
  rw [leastFactorTerm_eq_moebius]
  by_cases hd : 1 < d
  · rw [if_pos hd]
    by_cases hb : B < d.minFac
    · rw [if_pos ⟨hd,hb⟩,abs_mul]
      have hm : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      exact mul_le_one₀ hm (abs_nonneg _) (hg _)
    · rw [hzero _ (by omega),mul_zero,abs_zero,if_neg (by tauto)]
  · simp [hd]

lemma normalized_floor_error (N d : ℕ) (hN : 0 < N) :
    |((N/d : ℕ) : ℝ)/(N : ℝ)-1/(d : ℝ)| ≤ 1/(N : ℝ) := by
  by_cases hd : d=0
  · simp [hd]
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have he : ((N/d : ℕ) : ℝ)/(N : ℝ)-1/(d : ℝ) =
        -((N : ℝ)/d-((N/d : ℕ) : ℝ))/(N : ℝ) := by
      field_simp
      ring
    rw [he,abs_div,abs_neg,abs_of_pos hNr]
    exact div_le_div_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using nat_div_rounding_error_norm_le_one N d (by omega)) hNr.le

lemma normalized_floor_difference (M N d : ℕ) (hM : 0 < M) (hN : 0 < N) :
    |((M/d : ℕ) : ℝ)/(M : ℝ)-((N/d : ℕ) : ℝ)/(N : ℝ)| ≤
      1/(M : ℝ)+1/(N : ℝ) := by
  calc
    _ ≤ |((M/d : ℕ) : ℝ)/(M : ℝ)-1/(d : ℝ)|+
        |1/(d : ℝ)-((N/d : ℕ) : ℝ)/(N : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (normalized_floor_error M d hM)
      (by rw [abs_sub_comm]; exact normalized_floor_error N d hN)

/-- The bound is independent of the choice of bounded prime weights. -/
theorem primeMarginalMean_rough_endpoint_bound (g : ℕ → ℝ) (B M N : ℕ)
    (hB : 1 ≤ B) (hM : 0 < M) (hMN : M ≤ N)
    (hg : ∀ p, |g p| ≤ 1) (hzero : ∀ p, p ≤ B → g p=0) :
    |primeMarginalMean g M-primeMarginalMean g N| ≤
      (1/(M : ℝ)+1/(N : ℝ))*roughNumberCount B (N+1) := by
  have hN : 0 < N := hM.trans_le hMN
  rw [primeMarginalMean_floor_sum g (hzero 1 hB) M N hMN,
    primeMarginalMean_floor_sum g (hzero 1 hB) N N le_rfl]
  simp only [neg_div,sum_div]
  rw [neg_sub_neg,← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ range (N+1),
        |leastFactorTerm g d*(((N/d : ℕ) : ℝ)/(N : ℝ)-((M/d : ℕ) : ℝ)/(M : ℝ))| := by
      have he (d : ℕ) : leastFactorTerm g d*((N/d : ℕ) : ℝ)/(N : ℝ)-
          leastFactorTerm g d*((M/d : ℕ) : ℝ)/(M : ℝ) =
          leastFactorTerm g d*(((N/d : ℕ) : ℝ)/(N : ℝ)-((M/d : ℕ) : ℝ)/(M : ℝ)) := by ring
      simp_rw [he]
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ range (N+1),
        (if 1 < d ∧ B < d.minFac then (1 : ℝ) else 0)*(1/(M : ℝ)+1/(N : ℝ)) := by
      apply sum_le_sum
      intro d _
      rw [abs_mul]
      apply mul_le_mul (leastFactorTerm_rough_bound g B d hg hzero)
      · simpa only [add_comm] using normalized_floor_difference N M d hN hM
      · exact abs_nonneg _
      · split_ifs <;> norm_num
    _ = _ := by
      rw [← sum_mul]
      simp [roughNumberCount,mul_comm]

noncomputable def primeWeightHigh (B : ℕ) (g : ℕ → ℝ) (p : ℕ) : ℝ :=
  if B < p then g p else 0

lemma primeWeightHigh_bound (B : ℕ) (g : ℕ → ℝ) (hg : ∀ p, |g p| ≤ 1) :
    ∀ p, |primeWeightHigh B g p| ≤ 1 := by
  intro p
  unfold primeWeightHigh
  split_ifs <;> simp_all

lemma primeMarginalMean_truncation_bound (g : ℕ → ℝ) (B N X : ℕ) (hNX : N ≤ X)
    (hg : ∀ p, |g p| ≤ 1) :
    |primeMarginalMean g N-primeMarginalMean (primeWeightHigh B g) N| ≤
      ((((range X).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ)+2)/(N : ℝ) := by
  unfold primeMarginalMean
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (abs_sum_le_sum_abs _ _).trans
  have hb : (∑ n ∈ range N, |g (Nat.maxPrimeFac (n+1))-primeWeightHigh B g (Nat.maxPrimeFac (n+1))|) ≤
      ∑ n ∈ range X, if Nat.maxPrimeFac (n+1) ≤ B then (1 : ℝ) else 0 := by
    calc
      _ ≤ ∑ n ∈ range N, if Nat.maxPrimeFac (n+1) ≤ B then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro n _
        unfold primeWeightHigh
        split_ifs <;> simp_all
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono hNX) (fun _ _ _ => by split_ifs <;> norm_num)
  have hh := smooth_shifted_indicator_sum_le B X 1
  have hc : (((range (X+1)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
      (((range (X+2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset_filter _ (range_mono (by omega)))
  exact hb.trans ((hh.trans hc).trans (smooth_count_add_two_le B X))

/-- A finite one-coordinate estimate for arbitrary comparable endpoints. -/
theorem primeMarginalMean_endpoint_bound (g : ℕ → ℝ) (B M N : ℕ)
    (hB : 1 ≤ B) (hM : 0 < M) (hMN : M ≤ N) (hg : ∀ p, |g p| ≤ 1) :
    |primeMarginalMean g M-primeMarginalMean g N| ≤
      (1/(M : ℝ)+1/(N : ℝ))*
        ((((range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ)+2+
          roughNumberCount B (N+1)) := by
  have hh := primeMarginalMean_rough_endpoint_bound (primeWeightHigh B g) B M N hB hM hMN
    (primeWeightHigh_bound B g hg) (fun p hp => by simp [primeWeightHigh,not_lt.mpr hp])
  have he₁ := primeMarginalMean_truncation_bound g B M N hMN hg
  have he₂ := primeMarginalMean_truncation_bound g B N N le_rfl hg
  have ht₁ := abs_sub_le (primeMarginalMean g M) (primeMarginalMean (primeWeightHigh B g) M)
    (primeMarginalMean g N)
  have ht₂ := abs_sub_le (primeMarginalMean (primeWeightHigh B g) M)
    (primeMarginalMean (primeWeightHigh B g) N) (primeMarginalMean g N)
  rw [abs_sub_comm (primeMarginalMean (primeWeightHigh B g) N)] at ht₂
  calc
    _ ≤ (((((range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ)+2)/(M : ℝ))+
        ((1/(M : ℝ)+1/(N : ℝ))*roughNumberCount B (N+1)+
          ((((range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ)+2)/(N : ℝ)) := by linarith
    _ = _ := by ring

noncomputable def primeMarginalEndpointBudget (N : ℕ) : ℝ :=
  ((((range N).filter fun n => Nat.maxPrimeFac n ≤ subpowerCutoff N).card : ℝ)+2+
    roughNumberCount (subpowerCutoff N) (N+1))/(N : ℝ)

lemma primeMarginalEndpointBudget_tendsto_zero :
    Tendsto primeMarginalEndpointBudget atTop (𝓝 0) := by
  have ht := (subpowerCutoff_smooth_count_tendsto_zero.add
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))).add
    (growing_roughNumberCount_succ_tendsto subpowerCutoff subpowerCutoff_atTop)
  unfold primeMarginalEndpointBudget
  simpa only [add_div,add_zero] using ht

lemma primeMarginalMean_comparable_bound (g : ℕ → ℝ) (K M N : ℕ)
    (hB : 1 ≤ subpowerCutoff N) (hM : 0 < M) (hMN : M ≤ N) (hNM : N ≤ K*M)
    (hg : ∀ p, |g p| ≤ 1) :
    |primeMarginalMean g M-primeMarginalMean g N| ≤
      (K+1 : ℝ)*primeMarginalEndpointBudget N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hM.trans_le hMN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hinv : 1/(M : ℝ) ≤ (K : ℝ)/N := by
    apply (div_le_div_iff₀ hMr hNr).mpr
    simpa only [one_mul] using (show (N : ℝ) ≤ K*M by exact_mod_cast hNM)
  have hb := primeMarginalMean_endpoint_bound g (subpowerCutoff N) M N hB hM hMN hg
  apply hb.trans
  unfold primeMarginalEndpointBudget
  calc
    _ ≤ ((K : ℝ)/N+1/N)*
        ((((range N).filter fun n => Nat.maxPrimeFac n ≤ subpowerCutoff N).card : ℝ)+2+
          roughNumberCount (subpowerCutoff N) (N+1)) := by gcongr
    _ = _ := by ring

/-- Uniformity includes arbitrary endpoint-dependent weights on the exact
prime values, not only a fixed finite quantization. -/
theorem primeMarginalMean_comparable_tendsto_zero
    (g : ℕ → ℕ → ℝ) (hg : ∀ j p, |g j p| ≤ 1)
    (M N : ℕ → ℕ) (hM : Tendsto M atTop atTop) (hN : Tendsto N atTop atTop)
    (K : ℕ) (hc : ∀ᶠ j : ℕ in atTop, M j ≤ N j ∧ N j ≤ K*M j) :
    Tendsto (fun j => primeMarginalMean (g j) (M j)-primeMarginalMean (g j) (N j))
      atTop (𝓝 0) := by
  have ht := (primeMarginalEndpointBudget_tendsto_zero.comp hN).const_mul (K+1 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hc,hM.eventually_gt_atTop 0,
    (subpowerCutoff_atTop.comp hN).eventually_ge_atTop 1] with j hj hm hb
  simpa only [Real.norm_eq_abs,Function.comp_def] using
    primeMarginalMean_comparable_bound (g j) K (M j) (N j) hb hm hj.1 hj.2 (hg j)

#print axioms primeMarginalMean_endpoint_bound
#print axioms primeMarginalMean_comparable_tendsto_zero
end Erdos371
