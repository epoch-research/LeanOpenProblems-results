import Submission.Vaughan
import Submission.DivisorEnergy
import Submission.PrimePowerError
import Submission.ChebyshevPNT
import Submission.TailTopology

/-! Exact Vaughan decomposition of the actual two-Mangoldt correlation. The
second Mangoldt factor is retained; no one-prime exponential estimate is asserted
for the new bilinear terms. -/
namespace Erdos972CorrelationVaughan

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta Topology
open Erdos972Vaughan Erdos972DivisorEnergy Erdos972PrimePowerError Erdos972ChebyshevPNT Erdos972Topology

noncomputable def weightedSum (f : ArithmeticFunction ℝ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, f n * w n

lemma weightedSum_add (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (N : ℕ) :
    weightedSum (f + g) w N = weightedSum f w N + weightedSum g w N := by
  simp only [weightedSum, ArithmeticFunction.add_apply, add_mul, sum_add_distrib]

lemma weightedSum_sub (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (N : ℕ) :
    weightedSum (f - g) w N = weightedSum f w N - weightedSum g w N := by
  simp only [weightedSum, Erdos972Vaughan.sub_apply, sub_mul, sum_sub_distrib]

lemma weightedSum_convolution (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (N : ℕ) :
    weightedSum (f * g) w N =
      ∑ m ∈ Ioc 0 N, f m * ∑ n ∈ Ioc 0 (N / m), g n * w (m * n) := by
  have he (n : ℕ) : (f * g) n * w n =
      ∑ ab ∈ n.divisorsAntidiagonal, f ab.1 * g ab.2 * w (ab.1 * ab.2) := by
    rw [ArithmeticFunction.mul_apply, sum_mul]
    apply sum_congr rfl
    intro ab hab
    rw [(Nat.mem_divisorsAntidiagonal.mp hab).1]
  unfold weightedSum
  simp_rw [he]
  rw [sum_divisorsAntidiagonal_eq_sum_hyperbola (fun m n => f m * g n * w (m*n)) N]
  simp only [mul_sum, mul_assoc]

lemma weightedSum_convolution_support (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ)
    (R N : ℕ) (hf : ∀ n, R < n → f n = 0) :
    weightedSum (f * g) w N =
      ∑ m ∈ Ioc 0 (min R N), f m * ∑ n ∈ Ioc 0 (N / m), g n * w (m * n) := by
  rw [weightedSum_convolution]
  symm
  apply sum_subset
  · intro m hm
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans (min_le_right _ _)⟩
  · intro m hm hnot
    have hRm : R < m := by
      have hmN := mem_Ioc.mp hm
      simp only [mem_Ioc, le_min_iff, hmN.1, hmN.2, and_true, true_and] at hnot
      omega
    simp [hf m hRm]

noncomputable def outputError (α : ℝ) (n : ℕ) : ℝ := Λ (floorMul α n) - 1

noncomputable def firstTypeI (α : ℝ) (U N : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 (min U N), (μ m : ℝ) *
    ∑ n ∈ Ioc 0 (N / m), Real.log n * outputError α (m * n)

noncomputable def secondTypeI (α : ℝ) (U V N : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 (min (U * V) N),
    (cutoff (μ : ArithmeticFunction ℝ) U * cutoff Λ V) m *
      ∑ n ∈ Ioc 0 (N / m), outputError α (m * n)

noncomputable def typeII (α : ℝ) (U V N : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 N, (tail (μ : ArithmeticFunction ℝ) U * ζ) m *
    ∑ n ∈ Ioc 0 (N / m), tail Λ V n * outputError α (m * n)

noncomputable def smallTerm (α : ℝ) (V N : ℕ) : ℝ :=
  weightedSum (cutoff Λ V) (outputError α) N

lemma firstTypeI_eq (α : ℝ) (U N : ℕ) :
    weightedSum (cutoff (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log)
      (outputError α) N = firstTypeI α U N := by
  rw [weightedSum_convolution_support _ _ _ U N
    (fun n hn => cutoff_eq_zero_of_lt _ hn)]
  apply sum_congr rfl
  intro m hm
  rw [cutoff_eq_of_le _ ((mem_Ioc.mp hm).2.trans (min_le_left _ _))]
  rfl

lemma secondTypeI_eq (α : ℝ) (U V N : ℕ) :
    weightedSum (cutoff (μ : ArithmeticFunction ℝ) U * ζ * cutoff Λ V)
      (outputError α) N = secondTypeI α U V N := by
  have he : cutoff (μ : ArithmeticFunction ℝ) U * ζ * cutoff Λ V =
      (cutoff (μ : ArithmeticFunction ℝ) U * cutoff Λ V) * ζ := by ring
  rw [he, weightedSum_convolution_support _ _ _ (U * V) N
    (fun n hn => cutoff_mul_cutoff_eq_zero_of_lt _ _ U V n hn)]
  apply sum_congr rfl
  intro m hm
  congr 1
  apply sum_congr rfl
  intro n hn
  simp only [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1), Nat.cast_one, one_mul]

/-- Vaughan's identity applied to the two-prime correlation, rather than to a
single-prime Fourier sum. -/
theorem correlation_vaughan_identity (α : ℝ) (U V N : ℕ) :
    mangoldtCorrelation α N - Chebyshev.psi N =
      firstTypeI α U N - secondTypeI α U V N + smallTerm α V N + typeII α U V N := by
  have he := congrArg (fun f => weightedSum f (outputError α) N) (vaughan_identity U V)
  simp only [weightedSum_add, weightedSum_sub, firstTypeI_eq, secondTypeI_eq] at he
  have hc : weightedSum Λ (outputError α) N = mangoldtCorrelation α N - Chebyshev.psi N := by
    simp only [weightedSum, outputError, mul_sub, mul_one, sum_sub_distrib,
      mangoldtCorrelation, Chebyshev.psi, Nat.floor_natCast]
  rw [hc] at he
  rw [weightedSum_convolution] at he
  exact he

lemma abs_outputError_le {α : ℝ} (hα : 1 ≤ α) {n N : ℕ} (hn : n ∈ Ioc 0 N) :
    |outputError α n| ≤ Real.log (α * N) + 1 := by
  have h := vonMangoldt_le_log (n := floorMul α n) |>.trans (log_floorMul_le hα hn)
  have h0 := vonMangoldt_nonneg (n := floorMul α n)
  unfold outputError
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg h0, abs_one]
  linarith

lemma smallTerm_bound {α : ℝ} (hα : 1 ≤ α) (V : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |smallTerm α V N| ≤ Chebyshev.psi V * (Real.log (α * N) + 1) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (α * N) + 1 := by
    have := Real.log_nonneg (show 1 ≤ α * N by nlinarith)
    linarith
  unfold smallTerm weightedSum
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, cutoff Λ V n * (Real.log (α * N) + 1) := by
      apply sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (cutoff_vonMangoldt_nonneg V n)]
      exact mul_le_mul_of_nonneg_left (abs_outputError_le hα hn) (cutoff_vonMangoldt_nonneg V n)
    _ = (∑ n ∈ Ioc 0 (min V N), Λ n) * (Real.log (α * N) + 1) := by
      rw [← sum_mul]
      congr 1
      simp only [cutoff_apply, ← sum_filter]
      congr 1
      ext n
      simp only [mem_filter, mem_Ioc, le_min_iff]
      tauto
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hL
      simpa only [Chebyshev.psi, Nat.floor_natCast] using
        Chebyshev.psi_mono (Nat.cast_le.mpr (min_le_left V N))

noncomputable def vaughanBudget (α : ℝ) (U V N : ℕ) : ℝ :=
  |firstTypeI α U N| + |secondTypeI α U V N| +
    Chebyshev.psi V * (Real.log (α * N) + 1) + |typeII α U V N|

/-- An unconditional error bound, with the genuinely unestimated terms displayed
explicitly instead of replaced by one-prime exponential estimates. -/
theorem correlation_error_le_budget {α : ℝ} (hα : 1 ≤ α) (U V : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |mangoldtCorrelation α N - Chebyshev.psi N| ≤ vaughanBudget α U V N := by
  rw [correlation_vaughan_identity]
  apply (abs_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (abs_add_le _ _).trans
  exact add_le_add (abs_sub _ _) (smallTerm_bound hα V hN)

noncomputable def primePowerBudget (α : ℝ) (N : ℕ) : ℝ :=
  (Real.log 4 + 12) * (Real.log (α * N) * Real.sqrt N +
    Real.log N * Real.sqrt (α * N))

lemma primePowerBudget_div_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ => primePowerBudget α N / N) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log α / Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  simp_rw [← Real.sqrt_eq_rpow] at hl
  have hlN : Tendsto (fun N : ℕ => Real.log N / Real.sqrt N) atTop (𝓝 0) :=
    hl.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (Real.log 4 + 12) *
      (Real.log α / Real.sqrt N + (1 + Real.sqrt α) * (Real.log N / Real.sqrt N))) atTop (𝓝 0) := by
    simpa using (hc.add (hlN.const_mul (1 + Real.sqrt α))).const_mul (Real.log 4 + 12)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  unfold primePowerBudget
  rw [Real.log_mul hα0.ne' hN0.ne', Real.sqrt_mul hα0.le]
  field_simp
  ring_nf
  rw [Real.sq_sqrt hN0.le]

lemma primeCorrelation_bounded_of_finite {α : ℝ} (hfin : (primeSet α).Finite) :
    ∃ C : ℝ, ∀ N : ℕ, primeCorrelation α N ≤ C := by
  classical
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨primeCorrelation α B, ?_⟩
  intro N
  unfold primeCorrelation
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hpp, hqp⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, hB ⟨hpp, hqp⟩⟩, hpp, hqp⟩
  · intro p _ _
    exact mul_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg (floorMul α p))

/-- A counterexample would force the normalized actual Mangoldt correlation to
vanish. Prime powers alone contribute only a sublinear error. -/
theorem finite_primeSet_correlation_tendsto_zero {α : ℝ} (hα : 1 ≤ α)
    (hfin : (primeSet α).Finite) :
    Tendsto (fun N : ℕ => mangoldtCorrelation α N / N) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := primeCorrelation_bounded_of_finite hfin
  have hlim : Tendsto (fun N : ℕ => C / N + primePowerBudget α N / N) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).add (primePowerBudget_div_tendsto hα)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    apply div_nonneg _ (Nat.cast_nonneg N)
    exact sum_nonneg (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have he := (prime_power_error_bound_sharp hα hN).2
    change mangoldtCorrelation α N - primeCorrelation α N ≤ primePowerBudget α N at he
    have hh : mangoldtCorrelation α N ≤ C + primePowerBudget α N := by linarith [hC N]
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) N)

/-- A sublinear Vaughan budget on any sequence of growing cutoffs is sufficient
for genuine prime-pair infinitude at the given slope. The budget estimate is an
explicit hypothesis here, not a proved result for irrational slopes. -/
theorem infinite_primeSet_of_sublinear_budget {α : ℝ} (hα : 1 ≤ α)
    (U V N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hbudget : Tendsto (fun j => vaughanBudget α (U j) (V j) (N j) / N j) atTop (𝓝 0)) :
    (primeSet α).Infinite := by
  have herr : Tendsto (fun j => (mangoldtCorrelation α (N j) - Chebyshev.psi (N j)) / N j)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbudget
    filter_upwards [hN.eventually (eventually_ge_atTop (1 : ℕ))] with j hj
    simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (N j))]
    exact div_le_div_of_nonneg_right (correlation_error_le_budget hα (U j) (V j) hj)
      (Nat.cast_nonneg (N j))
  have hψ : Tendsto (fun j => Chebyshev.psi (N j) / N j) atTop (𝓝 1) :=
    psi_div_self_tendsto.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hmain : Tendsto (fun j => mangoldtCorrelation α (N j) / N j) atTop (𝓝 1) := by
    have he (j : ℕ) : (mangoldtCorrelation α (N j) - Chebyshev.psi (N j)) / N j +
        Chebyshev.psi (N j) / N j = mangoldtCorrelation α (N j) / N j := by ring
    simpa only [he, zero_add] using herr.add hψ
  intro hfin
  have hzero := (finite_primeSet_correlation_tendsto_zero hα hfin).comp hN
  have hcontra : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hmain
  norm_num at hcontra

/-- Conversely, a counterexample forces a linear obstruction in the displayed
Vaughan budget, uniformly over all choices of its two cutoffs. -/
theorem finite_primeSet_forces_linear_budget {α : ℝ} (hα : 1 ≤ α)
    (hfin : (primeSet α).Finite) :
    ∀ᶠ N : ℕ in atTop, ∀ U V : ℕ, (N : ℝ) / 2 ≤ vaughanBudget α U V N := by
  have hψ := psi_div_self_tendsto.comp tendsto_natCast_atTop_atTop
  have hc := finite_primeSet_correlation_tendsto_zero hα hfin
  have hlim : Tendsto (fun N : ℕ => (Chebyshev.psi N - mangoldtCorrelation α N) / N)
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, ← sub_div, sub_zero] using hψ.sub hc
  have hl := (tendsto_order.mp hlim).1 (1 / 2) (by norm_num)
  filter_upwards [hl, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  intro U V
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hh := (lt_div_iff₀ hN0).mp hN
  have he := correlation_error_le_budget hα U V hN1
  have ha := neg_le_abs (mangoldtCorrelation α N - Chebyshev.psi N)
  linarith

/-- When the small-input term is negligible, at least one genuinely bilinear
term must remain large at every sufficiently large scale of a counterexample. -/
theorem finite_primeSet_forces_large_bilinear_term {α : ℝ} (hα : 1 ≤ α)
    (hfin : (primeSet α).Finite) :
    ∀ᶠ N : ℕ in atTop, ∀ U V : ℕ,
      Chebyshev.psi V * (Real.log (α * N) + 1) ≤ (N : ℝ) / 8 →
      (N : ℝ) / 8 ≤ |firstTypeI α U N| ∨
      (N : ℝ) / 8 ≤ |secondTypeI α U V N| ∨
      (N : ℝ) / 8 ≤ |typeII α U V N| := by
  filter_upwards [finite_primeSet_forces_linear_budget hα hfin] with N hN
  intro U V hsmall
  have h := hN U V
  unfold vaughanBudget at h
  by_contra hn
  push_neg at hn
  linarith [hn.1, hn.2.1, hn.2.2]

#print axioms correlation_vaughan_identity
#print axioms correlation_error_le_budget
#print axioms infinite_primeSet_of_sublinear_budget
#print axioms finite_primeSet_forces_large_bilinear_term

end Erdos972CorrelationVaughan
