import Submission.SquarefreeDivisorExpansion
import Submission.DampedMeanZeta

/-! The full squarefree-support mean under the actual prime-output weight.
This is not a cancellation estimate for μ and does not settle Erdős 972. -/
namespace Erdos972SquarefreePrimeOutputMean

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972SquarefreeDivisorExpansion Erdos972SquarefreePrimeOutputBound
open Erdos972WeightedDivisorAmplification Erdos972PrimeOutputAmplificationScales
open Erdos972PrimeOutputDilationReduction Erdos972PrimeGcdRows
open Erdos972PrimePowerError Erdos972ChebyshevRowMean Erdos972CenteredRowScales
open Erdos972CovarianceScaleBudgets Erdos972CommonCovarianceScales
open Erdos972PolynomialRowScales Erdos972WeightedBeattyRows
open Erdos972PrimeCovarianceObstruction Erdos972DivisorCovariance
open Erdos972GrowingTypeI Erdos972GrowingTypeIIReduction
open Erdos972FixedDampedCorrelation Erdos972DampedMeanZeta Erdos972SmoothDivisorTail

set_option maxHeartbeats 2000000

lemma squarefreeMeanTruncation_eq (D : ℕ) :
    squarefreeMeanTruncation D = divisorMean D (dampedCoefficient 1) := by
  unfold squarefreeMeanTruncation divisorMean
  apply sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr (mem_Ioc.mp hd).1
  simp only [dampedCoefficient, neg_mul, one_mul, Real.exp_neg, Real.exp_log hdR]
  ring

lemma squarefreeMeanTruncation_tendsto :
    Tendsto squarefreeMeanTruncation atTop (𝓝 (6/Real.pi^2)) := by
  have hz := zeta_mul_dampedMean (by norm_num : (0 : ℝ) < 1)
  norm_num only [Complex.ofReal_one, one_add_one_eq_two] at hz
  rw [riemannZeta_two] at hz
  have hzR : (Real.pi^2/6)*dampedMean 1 = 1 := by
    exact_mod_cast hz
  have he : dampedMean 1 = 6/Real.pi^2 := by
    apply (eq_div_iff (pow_ne_zero 2 Real.pi_ne_zero)).mpr
    nlinarith only [hzR]
  simpa only [← squarefreeMeanTruncation_eq, he] using
    (divisorMean_tendsto (by norm_num : (0 : ℝ) < 1))

lemma growingCutoff_log_div_tendsto (C : ℝ) (hC : 0 < C) (k : ℕ) :
    Tendsto (fun u : ℕ => C*(1+Real.log u)^k/(growingCutoff u : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlim := root64_log_div_tendsto (4*C^2) (by positivity) (2*k)
  filter_upwards [(tendsto_order.mp hlim).2 (ε^2) (sq_pos_of_pos hε),
    growingCutoff_tendsto.eventually_ge_atTop 1] with u he hW
  have hWR : (1 : ℝ) ≤ growingCutoff u := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < growingCutoff u := by linarith
  have hv0 : (0 : ℝ) < root64 u := hW0.trans_le
    (Nat.cast_le.mpr (growingCutoff_eligible u).1)
  have hvW : (root64 u : ℝ) ≤ 4*(growingCutoff u : ℝ)^2 := by
    have hh := Nat.lt_succ_sqrt' (root64 u)
    have hhR : (root64 u : ℝ) < ((growingCutoff u : ℝ)+1)^2 := by exact_mod_cast hh
    nlinarith only [hhR, hWR, sq_nonneg ((growingCutoff u : ℝ)-1)]
  have hh := (div_lt_iff₀ hv0).mp he
  rw [show 2*k = k*2 by omega, pow_mul] at hh
  have hscale := mul_le_mul_of_nonneg_left hvW (sq_nonneg ε)
  have hLp : 0 ≤ C*(1+Real.log u)^k := by positivity [Real.log_natCast_nonneg u]
  have hgoal : C*(1+Real.log u)^k < ε*(growingCutoff u : ℝ) := by
    nlinarith only [hh, hscale, hLp, mul_pos hε hW0]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hLp hW0.le)]
  exact (div_lt_iff₀ hW0).mpr hgoal

lemma squarefree_row_budget_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun u : ℕ => (growingCutoff u : ℝ)*outputRowBudget α u /
      (scaleCutoff α u : ℝ)) atTop (𝓝 0) := by
  have hh := scale_log_weight_tendsto hα 1 (by norm_num : (0 : ℝ) ≤ 8)
    (fun u => polynomialRowError u (root64 u)+1)
    (by intro u; unfold polynomialRowError; positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u])
    (summed_polynomialRowError_add_one_tendsto 1)
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hu huα
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hlog : 0 ≤ Real.log (α*scaleCutoff α u) := by
    have hl := (scale_log_bound hα hu hαu).1
    linarith only [hl]
  have hE : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  have hbud : 0 ≤ outputRowBudget α u := by unfold outputRowBudget; positivity
  have hle : outputRowBudget α u ≤
      8*(1+Real.log (α*scaleCutoff α u))*(polynomialRowError u (root64 u)+1) := by
    unfold outputRowBudget
    nlinarith only [hE, hlog, mul_nonneg hE hlog]
  have hWv : (growingCutoff u : ℝ) ≤ root64 u := Nat.cast_le.mpr (growingCutoff_eligible u).1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hm := mul_le_mul hWv hle hbud (Nat.cast_nonneg (root64 u))
  simpa only [pow_one, mul_assoc, mul_left_comm, mul_comm] using hm

lemma squarefree_tail_budget_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun u : ℕ => Real.log (α*scaleCutoff α u)/(growingCutoff u : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (growingCutoff_log_div_tendsto 6 (by norm_num) 1)
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hu huα
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hlogs := scale_log_bound hα hu hαu
  have hlog : 0 ≤ Real.log (α*scaleCutoff α u) := by linarith only [hlogs.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [pow_one]
  linarith only [hlogs.2]

noncomputable def squarefreeOutputSum (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, outputWeight α n * |(moebius n : ℝ)|

lemma squarefree_output_error {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {u : ℕ} (hu : 0 < u) (hαu : α ≤ u) (hW : 0 < growingCutoff u)
    (hrows : OutputPrimeScale α u) :
    |squarefreeOutputSum α (scaleCutoff α u) -
      rowMean α (scaleCutoff α u)*squarefreeMeanTruncation (growingCutoff u)| ≤
      Real.log (α*scaleCutoff α u)*(scaleCutoff α u : ℝ)/(growingCutoff u : ℝ) +
        (growingCutoff u : ℝ)*outputRowBudget α u := by
  have huN := (scaleCutoff_bounds hα.le hu hαu).1
  have hN : 0 < scaleCutoff α u := hu.trans_le huN
  have hvN : root64 u ≤ scaleCutoff α u :=
    ((Nat.le_self_pow (by decide : 64 ≠ 0) (root64 u)).trans (root64_bounds hu).2.1).trans huN
  have hWN := (growingCutoff_eligible u).1.trans hvN
  have hlog : 0 ≤ Real.log (α*scaleCutoff α u) := by
    have hh := (scale_log_bound hα.le hu hαu).1
    linarith only [hh]
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  apply weighted_squarefree_mean_error (outputWeight α) hW hWN hlog
    (fun n _ => vonMangoldt_nonneg)
  · intro n hn
    exact vonMangoldt_le_log.trans (log_floorMul_le hα.le hn)
  · intro d hd
    have hd0 := (mem_Ioc.mp hd).1
    have hdW := (mem_Ioc.mp hd).2
    have hd2v : d^2 ≤ root64 u :=
      (Nat.pow_le_pow_left hdW 2).trans (by simpa only [pow_two] using (growingCutoff_eligible u).2)
    have hh := prime_divisor_prefix_error hα hI hE0 hN (pow_pos hd0 2)
      (j := scaleCutoff α u) le_rfl (by
        intro Q hQ
        rw [outputRow_mangoldt]
        exact hrows (d^2) (pow_pos hd0 2) hd2v Q
          (hQ.trans (scaleCutoff_row_eligible hα.le u (d^2) (scaleCutoff α u/(d^2)) le_rfl)))
    exact hh.trans (by unfold outputRowBudget; linarith)

/-- The normalized absolute Möbius-support mean tends to 6/pi² along the
actual good scales. This controls support, not the sign of μ. -/
theorem eventually_squarefree_output_mean {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, OutputPrimeScale α u →
      |squarefreeOutputSum α (scaleCutoff α u)/(scaleCutoff α u : ℝ)-6/Real.pi^2| ≤ ε := by
  have hα0 : 0 < α := by linarith
  have hb := (squarefree_tail_budget_tendsto hα.le).add (squarefree_row_budget_tendsto hα.le)
  simp only [add_zero] at hb
  have hm := ((rowMean_div_tendsto hα0).comp (scaleCutoff_tendsto hα.le)).mul
    (squarefreeMeanTruncation_tendsto.comp growingCutoff_tendsto)
  simp only [Function.comp_apply, one_mul] at hm
  have hm' := (hm.sub_const (6/Real.pi^2)).abs
  simp only [sub_self, abs_zero] at hm'
  filter_upwards [(tendsto_order.mp hb).2 (ε/2) (by positivity),
    (tendsto_order.mp hm').2 (ε/2) (by positivity),
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊,
    growingCutoff_tendsto.eventually_ge_atTop 1] with u hbudget hmain hu huα hW
  intro hrows
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hN : 0 < scaleCutoff α u := (show 0 < u from hu).trans_le (scaleCutoff_bounds hα.le hu hαu).1
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have herr := div_le_div_of_nonneg_right (squarefree_output_error hα hI hu hαu hW hrows) hNR.le
  have hid : (Real.log (α*scaleCutoff α u)*(scaleCutoff α u : ℝ)/(growingCutoff u : ℝ) +
        (growingCutoff u : ℝ)*outputRowBudget α u)/(scaleCutoff α u : ℝ) =
      Real.log (α*scaleCutoff α u)/(growingCutoff u : ℝ) +
        (growingCutoff u : ℝ)*outputRowBudget α u/(scaleCutoff α u : ℝ) := by
    field_simp
  rw [hid] at herr
  have he : squarefreeOutputSum α (scaleCutoff α u)/(scaleCutoff α u : ℝ)-6/Real.pi^2 =
      (squarefreeOutputSum α (scaleCutoff α u)-
        rowMean α (scaleCutoff α u)*squarefreeMeanTruncation (growingCutoff u))/(scaleCutoff α u : ℝ) +
      (rowMean α (scaleCutoff α u)/(scaleCutoff α u : ℝ)*
        squarefreeMeanTruncation (growingCutoff u)-6/Real.pi^2) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos hNR]
  linarith only [herr, hbudget, hmain]

/-- An unconditional arbitrarily-large-scale version of the preceding mean. -/
theorem exists_squarefree_output_mean {α ε : ℝ} (hα : 1 < α) (hI : Irrational α)
    (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ |squarefreeOutputSum α N/(N : ℝ)-6/Real.pi^2| ≤ ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_squarefree_output_mean hα hI hε)
  obtain ⟨u, hu, hαu, hv, hrows, _⟩ := exists_joint_prime_divisor_scale hα hI (max B T)
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith
  refine ⟨scaleCutoff α u, ((le_max_left B T).trans_lt hu).trans_le
    (scaleCutoff_bounds hα.le hu0 hαu').1, ?_⟩
  exact hT u ((le_max_right B T).trans hu.le) hrows

lemma moebius_output_le_squarefree_support (α : ℝ) (N : ℕ) :
    |moebiusOutputSum α N| ≤ squarefreeOutputSum α N := by
  unfold moebiusOutputSum squarefreeOutputSum
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [abs_mul, abs_of_nonneg (show 0 ≤ outputWeight α n from vonMangoldt_nonneg)]

/-- The resulting optimal squarefree-support constant. It remains a bound
by a positive constant times N, and is not a prime-pair lower bound. -/
theorem exists_moebius_output_euler_support_bound {α ε : ℝ} (hα : 1 < α)
    (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ |moebiusOutputSum α N| ≤ (6/Real.pi^2+ε)*N := by
  obtain ⟨N, hBN, hmean⟩ := exists_squarefree_output_mean hα hI hε B
  have hN : 0 < N := (Nat.zero_le B).trans_lt hBN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh : squarefreeOutputSum α N/(N : ℝ) ≤ 6/Real.pi^2+ε := by
    have h := (abs_le.mp hmean).2
    linarith only [h]
  exact ⟨N, hBN, (moebius_output_le_squarefree_support α N).trans ((div_le_iff₀ hNR).mp hh)⟩

/-- Taking absolute values cannot itself yield o(N) for this actual weight.
This does not rule out cancellation in the signed Möbius sum. -/
theorem not_tendsto_squarefree_output_zero {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    ¬ Tendsto (fun N : ℕ => squarefreeOutputSum α N/(N : ℝ)) atTop (𝓝 0) := by
  intro hz
  let c : ℝ := 6/Real.pi^2
  have hc : 0 < c := by dsimp [c]; positivity [Real.pi_pos]
  obtain ⟨B, hB⟩ := eventually_atTop.mp ((tendsto_order.mp hz).2 (c/2) (by positivity))
  obtain ⟨N, hBN, he⟩ := exists_squarefree_output_mean hα hI (show 0 < c/4 by positivity) B
  have hsmall := hB N hBN.le
  have hlarge := (abs_le.mp he).1
  change -(c/4) ≤ squarefreeOutputSum α N/(N : ℝ)-c at hlarge
  linarith only [hsmall, hlarge, hc]

#print axioms not_tendsto_squarefree_output_zero

#print axioms squarefreeMeanTruncation_tendsto
#print axioms squarefree_row_budget_tendsto
#print axioms squarefree_tail_budget_tendsto
#print axioms squarefree_output_error
#print axioms eventually_squarefree_output_mean
#print axioms exists_squarefree_output_mean
#print axioms exists_moebius_output_euler_support_bound

end Erdos972SquarefreePrimeOutputMean
