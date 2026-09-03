import Submission.ContinuousIntervalQuantumEffectiveBudget
import Submission.ContinuousIntervalQuantumLogBudget
import Submission.ContinuousIntervalPolynomialBarrier

/-! Every schedule of guarded quantum refinements (without chord patches)
is dominated by one fixed dilation of the ordinary reference recurrence.
The constant is uniform in the schedule and the stage. This is a comparison
of algorithms, not a positivity theorem or a settlement of Erdős 970. -/
namespace Erdos970.ContinuousInterval
open Finset Real Filter
set_option maxHeartbeats 2000000

lemma actualQuantumDilationBudget_eventually_rpow (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, actualQuantumDilationBudget k ≤ (k : ℝ)^η := by
  obtain ⟨C,hC,hbudget⟩ := actualQuantumDilationBudget_eventually_log 1 (by norm_num)
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop hη).def (show (0 : ℝ) < 1/C by positivity))
  filter_upwards [hbudget,hsmall,eventually_ge_atTop 1] with k hb hs hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs' : log (k : ℝ) ≤ (1/C)*(k : ℝ)^η := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (log_natCast_nonneg k),
      abs_of_pos (rpow_pos_of_pos hk0 η)] using hs
  rw [rpow_one] at hb
  have hh := mul_le_mul_of_nonneg_left hs' hC.le
  have he : C*((1/C)*(k : ℝ)^η)=(k : ℝ)^η := by field_simp
  rw [he] at hh
  exact hb.trans hh

/-- Successful trigger lengths are uniformly superlinear. Failures are
permitted and are not charged by the effective product. -/
theorem eventually_active_trigger_superlinear : ∃ η > (0 : ℝ),
    ∀ᶠ i : ℕ in atTop, ∀ trigger : ℕ → ℕ,
      quantumTriggerActive (fun i => (referenceMarginal i : ℝ)) trigger i →
      (((i+1 : ℕ) : ℝ)^(1+η)) < trigger i := by
  obtain ⟨δ,hδ,hzero⟩ := exists_polynomial_ordinary_zero_barrier
  let η := δ/2
  have hη : 0 < η := by dsimp [η]; positivity
  have hb := actualQuantumDilationBudget_eventually_rpow η hη
  refine ⟨η,hη,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (hzero.and hb)] with i hi
  intro trigger hactive
  let Q := fun i => (referenceMarginal i : ℝ)
  let K := i+1
  let D := actualQuantumDilationBudget K
  have hK : (0 : ℝ) < K := by dsimp [K]; positivity
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (actualQuantumDilationBudget_one_le K)
  have hdom := quantumReference_actual_dilation trigger K
  have hpatch := quantumRefine_dominates (density Q K) (trigger i)
    (quantumPreLower Q trigger i)
    (stepUpper (Q i) (quantumEnvelope Q (fun _ => []) trigger i).1
      (quantumEnvelope Q (fun _ => []) trigger i).2)
  have hpost : 0 < (quantumEnvelope Q (fun _ => []) trigger K).1 (trigger i) :=
    hactive.2.2.2.trans_le (hpatch.1 (trigger i))
  have hpdiv := hpost.trans_le (hdom.1 (trigger i))
  have hnum : 0 < (envelope Q K (D*(trigger i : ℝ))).1 := by
    by_contra hh
    have hn := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hD.le
    exact hpdiv.not_ge hn
  by_contra hh
  have hg : (trigger i : ℝ) ≤ (K : ℝ)^(1+η) := le_of_not_gt hh
  have hmul := mul_le_mul hi.2 hg (Nat.cast_nonneg (trigger i)) (rpow_nonneg hK.le η)
  have he : (K : ℝ)^η*(K : ℝ)^(1+η)=(K : ℝ)^(1+δ) := by
    rw [← rpow_add hK]
    congr 1
    dsimp [η]
    ring
  rw [he] at hmul
  have hm := (envelope_regular Q K (fun i _ => referenceMarginal_real_bounds i)).lower_mono hmul
  rw [hi.1] at hm
  exact hnum.not_ge hm

lemma eventually_effectiveQuantumFactor_exp_decay : ∃ η > (0 : ℝ),
    ∀ᶠ i : ℕ in atTop, ∀ trigger : ℕ → ℕ,
      effectiveQuantumFactor (fun i => (referenceMarginal i : ℝ)) trigger i ≤
        exp (4/(((i+1 : ℕ) : ℝ)^(1+η))) := by
  obtain ⟨η,hη,hh⟩ := eventually_active_trigger_superlinear
  refine ⟨η,hη,?_⟩
  filter_upwards [hh] with i hi
  intro trigger
  unfold effectiveQuantumFactor
  split_ifs with hactive
  · have hg := quantumTriggerActive_gt_stage _ trigger i referenceMarginal_real_bounds hactive
    have hgR : (2 : ℝ) ≤ trigger i := by exact_mod_cast (show 2 ≤ trigger i by omega)
    have hkpow : 0 < (((i+1 : ℕ) : ℝ)^(1+η)) := rpow_pos_of_pos (by positivity) _
    have hbig := hi trigger hactive
    have hrec : 2/((trigger i : ℝ)-1) ≤ 4/(((i+1 : ℕ) : ℝ)^(1+η)) := by
      apply (div_le_div_iff₀ (by linarith) hkpow).mpr
      linarith only [hbig,hgR]
    rw [quantumDilationFactor_eq_one_add (by omega : 1 < trigger i)]
    apply le_trans _ (exp_le_exp.mpr hrec)
    simpa only [add_comm] using add_one_le_exp (2/((trigger i : ℝ)-1))
  · exact one_le_exp (by positivity)

/-- A single finite constant bounds all effective products, uniformly over
all guarded trigger schedules. No summability of 1/h(k) is assumed. -/
theorem effectiveQuantumDilationBudget_uniform_bound : ∃ C > (0 : ℝ),
    ∀ trigger : ℕ → ℕ, ∀ k : ℕ,
      effectiveQuantumDilationBudget (fun i => (referenceMarginal i : ℝ)) trigger k ≤ C := by
  obtain ⟨η,hη,hh⟩ := eventually_effectiveQuantumFactor_exp_decay
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  let u := fun i : ℕ => 4/(((i+1 : ℕ) : ℝ)^(1+η))+(if i<N then 2 else 0)
  have hu : ∀ i, 0 ≤ u i := by
    intro i
    dsimp [u]
    positivity
  have hu1 : Summable (fun i : ℕ => 4/(((i+1 : ℕ) : ℝ)^(1+η))) := by
    have hs := (summable_nat_add_iff 1).mpr
      (summable_one_div_nat_rpow.mpr (show (1 : ℝ) < 1+η by linarith))
    convert hs.mul_left 4 using 1 <;> simp only [mul_one_div]
  have hu2 : Summable (fun i : ℕ => if i<N then (2 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := range N)
    intro i hi
    exact if_neg (fun hh => hi (mem_range.mpr hh))
  have hsum : Summable u := hu1.add hu2
  have hf : ∀ trigger : ℕ → ℕ, ∀ i,
      effectiveQuantumFactor (fun i => (referenceMarginal i : ℝ)) trigger i ≤ exp (u i) := by
    intro trigger i
    by_cases hi : N ≤ i
    · simpa only [u,if_neg (show ¬i<N by omega),add_zero] using hN i hi trigger
    · have hthree := effectiveQuantumFactor_le_three _ trigger i referenceMarginal_real_bounds
      have he : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
      apply (hthree.trans he).trans
      apply exp_le_exp.mpr
      dsimp only [u]
      rw [if_pos (show i<N by omega)]
      exact le_add_of_nonneg_left (by positivity)
  refine ⟨exp (∑' i, u i),exp_pos _,fun trigger k => ?_⟩
  have hprod := prod_le_prod
    (fun i hi => (by norm_num : (0 : ℝ) ≤ 1).trans
      (effectiveQuantumFactor_one_le _ trigger i referenceMarginal_real_bounds))
    (fun i (_hi : i ∈ range k) => hf trigger i)
  change (∏ i ∈ range k, effectiveQuantumFactor _ trigger i) ≤ _
  apply hprod.trans
  rw [← exp_sum]
  exact exp_le_exp.mpr (hsum.sum_le_tsum (range k) (fun i _ => hu i))

/-- Every guarded quantum schedule is dominated by one fixed dilation of
the ordinary reference envelope. The comparison is simultaneous in all
stages and lengths, but does NOT allow subsequent chord patches. -/
theorem quantumReference_bounded_dilation : ∃ C > (0 : ℝ),
    ∀ trigger : ℕ → ℕ, ∀ k : ℕ,
      Dominates
        (fun x => (envelope (fun i => (referenceMarginal i : ℝ)) k (C*x)).1/C)
        (fun x => (envelope (fun i => (referenceMarginal i : ℝ)) k (C*x)).2/C)
        (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) (fun _ => []) trigger k).1
        (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) (fun _ => []) trigger k).2 := by
  obtain ⟨C,hC,hbound⟩ := effectiveQuantumDilationBudget_uniform_bound
  refine ⟨C,hC,fun trigger k => ?_⟩
  have hB : 0 < effectiveQuantumDilationBudget (fun i => (referenceMarginal i : ℝ)) trigger k :=
    lt_of_lt_of_le (by norm_num) (effectiveQuantumDilationBudget_one_le _ trigger k
      referenceMarginal_real_bounds)
  have hr := envelope_regular (fun i => (referenceMarginal i : ℝ)) k
    (fun i _ => referenceMarginal_real_bounds i)
  exact (hr.dilation_mono _ _ hB (hbound trigger k)).trans
    (quantumEnvelope_effective_dilation _ trigger k referenceMarginal_real_bounds)

#print axioms eventually_active_trigger_superlinear
#print axioms effectiveQuantumDilationBudget_uniform_bound
#print axioms quantumReference_bounded_dilation
end Erdos970.ContinuousInterval
