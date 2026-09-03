import Submission.PowerThresholdNeighborSkew

/-! The actual density conjecture is equivalent to cancellation of an
arbitrarily fine sum of neighboring moving smooth-cutoff skews. The endpoint
error below is uniform even in the number of quantization levels. -/
namespace Erdos371
open Finset Filter FiniteInformation FixedPrimeAvoidance
open scoped Topology

noncomputable def neighborSmoothMean (Q N : ℕ) : ℝ :=
  (∑ t ∈ range (Q-1),
    smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N)/N

lemma quantFactorSign_zero (Q N : ℕ) : quantFactorSign Q N 0 = 0 := by
  simp [quantFactorSign,orderSkew,primeQuantLabel,unitQuantize,normalizedPrimeLog,primeLog]

lemma quantThreshold_one (Q N t : ℕ) : quantThreshold Q N t 1 = 1 := by
  simp [quantThreshold,thresholdStep,primeQuantLabel,unitQuantize,normalizedPrimeLog,primeLog]

lemma quantFactorSign_smooth_boundary (Q N : ℕ) (hQ : 0 < Q) (hN : 1 < N) :
    (∑ n ∈ range N, quantFactorSign Q N n) =
      (∑ t ∈ range (Q-1),
        smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N)+
      1-quantThreshold Q N (Q-1) (N+1)-quantFactorSign Q N N := by
  have he := sum_range_succ' (quantFactorSign Q N) N
  rw [sum_range_succ,quantFactorSign_zero,add_zero] at he
  have hp : (∑ n ∈ range N, quantFactorSign Q N (n+1)) =
      (∑ t ∈ range (Q-1),
        smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N)+
      1-quantThreshold Q N (Q-1) (N+1) := by
    simp_rw [quantFactorSign_neighbor_expansion]
    rw [sum_comm]
    conv_lhs => arg 1; rw [← Nat.sub_add_cancel hQ]
    rw [sum_range_succ]
    have hi : (∑ t ∈ range (Q-1), ∑ n ∈ range N, quantNeighborSkew Q N t (n+1)) =
        ∑ t ∈ range (Q-1),
          smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N := by
      apply sum_congr rfl
      intro t ht
      unfold smoothCutoffSkew
      apply sum_congr rfl
      intro n _
      simpa only [Nat.add_assoc] using quantNeighborSkew_eq_smooth_point Q N t (n+1) hN
        (by have := mem_range.mp ht; omega)
    rw [hi]
    simp_rw [quantNeighborSkew_top Q N _ hQ]
    rw [sum_range_sub' (fun n => quantThreshold Q N (Q-1) (n+1)) N,quantThreshold_one]
    ring
  rw [hp] at he
  linarith

lemma threshold_order_boundary_abs_le (Q a b : ℕ) (hQ : 0 < Q) (ha : a ≤ Q) (hb : b ≤ Q) :
    |1-thresholdStep (Q-1) b-orderSkew a b| ≤ 1 := by
  unfold thresholdStep orderSkew
  split_ifs <;> (first | omega | norm_num)

/-- There is only one bounded endpoint correction, independent of Q. -/
theorem quantized_neighborSmooth_error (Q N : ℕ) (hQ : 0 < Q) (hN : 1 < N) :
    |prefixMean N (quantFactorSign Q N)-neighborSmoothMean Q N| ≤ 1/(N : ℝ) := by
  unfold prefixMean neighborSmoothMean
  rw [← sub_div,quantFactorSign_smooth_boundary Q N hQ hN]
  have he : (∑ t ∈ range (Q-1),
      smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N)+
      1-quantThreshold Q N (Q-1) (N+1)-quantFactorSign Q N N-
      (∑ t ∈ range (Q-1),
        smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N) =
      1-quantThreshold Q N (Q-1) (N+1)-quantFactorSign Q N N := by ring
  rw [he,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have h := threshold_order_boundary_abs_le Q (primeQuantLabel Q N N).val
    (primeQuantLabel Q N (N+1)).val hQ (Nat.le_of_lt_succ (primeQuantLabel Q N N).isLt)
    (Nat.le_of_lt_succ (primeQuantLabel Q N (N+1)).isLt)
  simpa only [quantThreshold,quantFactorSign,orderSkew,Fin.lt_def] using h

/-- A sparse, exact reformulation of the conjecture. The smooth cutoffs vary
with N; fixed-cutoff symmetry cannot be substituted for this condition. -/
theorem density_iff_fine_neighbor_smooth_cancellation :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      ∀ ε : ℝ, 0 < ε → ∀ Q₀ : ℕ, ∃ Q ≥ Q₀, 0 < Q ∧
        ∀ᶠ N : ℕ in atTop, |neighborSmoothMean Q N| ≤ ε := by
  rw [density_iff_arbitrarily_fine_quantized_cancellation]
  constructor
  · intro hc ε hε Q₀
    obtain ⟨Q,hQQ,hQ,hc⟩ := hc (ε/2) (by positivity) Q₀
    refine ⟨Q,hQQ,hQ,?_⟩
    filter_upwards [hc,eventually_gt_atTop (1 : ℕ),
      tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)]
      with N hc hN he
    have hb := quantized_neighborSmooth_error Q N hQ hN
    have ht := abs_sub_le (neighborSmoothMean Q N) (prefixMean N (quantFactorSign Q N)) 0
    simp only [sub_zero] at ht
    rw [abs_sub_comm] at hb
    linarith
  · intro hc ε hε Q₀
    obtain ⟨Q,hQQ,hQ,hc⟩ := hc (ε/2) (by positivity) Q₀
    refine ⟨Q,hQQ,hQ,?_⟩
    filter_upwards [hc,eventually_gt_atTop (1 : ℕ),
      tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)]
      with N hc hN he
    have hb := quantized_neighborSmooth_error Q N hQ hN
    have ht := abs_sub_le (prefixMean N (quantFactorSign Q N)) (neighborSmoothMean Q N) 0
    simp only [sub_zero] at ht
    linarith

/-- It suffices to prove moving-cutoff reversal for each neighboring pair
in arbitrarily fine quantizations. These arithmetic hypotheses are unproved. -/
theorem density_of_neighboring_smooth_skew_cancellation
    (hc : ∀ Q₀ : ℕ, ∃ Q ≥ Q₀, 0 < Q ∧ ∀ t < Q-1,
      Tendsto (fun N : ℕ =>
        smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N/N)
        atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_fine_neighbor_smooth_cancellation]
  intro ε hε Q₀
  obtain ⟨Q,hQQ,hQ,hs⟩ := hc Q₀
  refine ⟨Q,hQQ,hQ,?_⟩
  have ht := tendsto_finset_sum (range (Q-1)) (fun t ht => hs t (mem_range.mp ht))
  simp only [sum_const_zero,← sum_div] at ht
  have he := (Metric.tendsto_nhds.mp ht) ε hε
  filter_upwards [he] with N hN
  rw [Real.dist_eq,sub_zero] at hN
  exact hN.le

#print axioms quantized_neighborSmooth_error
#print axioms density_iff_fine_neighbor_smooth_cancellation
#print axioms density_of_neighboring_smooth_skew_cancellation
end Erdos371
