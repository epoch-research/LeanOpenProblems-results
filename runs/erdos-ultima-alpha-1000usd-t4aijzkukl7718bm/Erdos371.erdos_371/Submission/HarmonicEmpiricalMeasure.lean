import Submission.HarmonicWindowDilation

/-! Harmonic empirical probability measures and their fixed-shift error.
This file constructs genuine finite measures; no stationary limit is assumed. -/
namespace Erdos371.FiniteInformation
open Finset Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
set_option autoImplicit false

lemma harmonicMean_succ_error (N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |harmonicMean (N+1) (fun n => F (n+1))-harmonicMean (N+1) F| ≤
      2/(harmonic (N+1) : ℝ) := by
  have h := harmonic_range_Icc_sum_error N (fun n => F (n+1)) (fun n => hF (n+1))
  have he : (∑ n ∈ range (N+1), F (n+1)/(n+1 : ℝ)) = ∑ n ∈ Icc 1 (N+1), F n/(n : ℝ) := by
    rw [sum_Icc_one_eq_sum_range]
    simp only [Nat.cast_add,Nat.cast_one]
  rw [he,abs_sub_comm] at h
  rw [harmonicMean,harmonicMean,← sub_div,abs_div,abs_of_pos (harmonic_real_pos N)]
  exact div_le_div_of_nonneg_right h (harmonic_real_pos N).le

lemma harmonicMean_succ_difference_zero (F : ℕ → ℝ) (B : ℝ) (hB : 0 < B)
    (hF : ∀ n, |F n| ≤ B) :
    Tendsto (fun N => harmonicMean (N+1) (fun n => F (n+1))-harmonicMean (N+1) F)
      atTop (𝓝 0) := by
  let G := fun n => F n/B
  have hG : ∀ n, |G n| ≤ 1 := by
    intro n
    dsimp only [G]
    rw [abs_div,abs_of_pos hB]
    exact (div_le_one hB).mpr (hF n)
  have ht : Tendsto (fun N => harmonicMean (N+1) (fun n => G (n+1))-harmonicMean (N+1) G)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => (2 : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop harmonic_real_tendsto
    apply squeeze_zero_norm _ hb
    intro N
    simpa only [Real.norm_eq_abs] using harmonicMean_succ_error N G hG
  have hf (n : ℕ) : B*G n = F n := by dsimp [G]; field_simp
  convert ht.const_mul B using 1
  · funext N
    rw [mul_sub,← harmonicMean_const_mul,← harmonicMean_const_mul]
    simp_rw [hf]
  · simp

noncomputable def harmonicWeight (N n : ℕ) : ℝ :=
  (1/(n : ℝ))/(harmonic (N+1) : ℝ)

lemma harmonicWeight_nonneg (N n : ℕ) : 0 ≤ harmonicWeight N n := by
  unfold harmonicWeight
  exact div_nonneg (by positivity) (harmonic_real_pos N).le

lemma harmonicWeight_sum (N : ℕ) : ∑ n ∈ Icc 1 (N+1), harmonicWeight N n = 1 := by
  unfold harmonicWeight
  rw [← sum_div]
  have hh : (∑ n ∈ Icc 1 (N+1), (1 : ℝ)/n) = harmonic (N+1) := by
    rw [harmonic_eq_sum_Icc]
    simp
  rw [hh,div_self (harmonic_real_pos N).ne']

variable {X : Type*} [MeasurableSpace X]

noncomputable def harmonicEmpiricalRaw (N : ℕ) (x : ℕ → X) : Measure X :=
  ∑ n ∈ Icc 1 (N+1), ENNReal.ofReal (harmonicWeight N n) • Measure.dirac (x n)

lemma harmonicEmpiricalRaw_univ (N : ℕ) (x : ℕ → X) : harmonicEmpiricalRaw N x Set.univ = 1 := by
  rw [harmonicEmpiricalRaw,Measure.finset_sum_apply]
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => harmonicWeight_nonneg N n),harmonicWeight_sum]
  norm_num

noncomputable def harmonicEmpirical (N : ℕ) (x : ℕ → X) : ProbabilityMeasure X :=
  ⟨harmonicEmpiricalRaw N x,⟨harmonicEmpiricalRaw_univ N x⟩⟩

lemma integral_harmonicEmpirical [MeasurableSingletonClass X] (N : ℕ) (x : ℕ → X) (F : X → ℝ) :
    (∫ y, F y ∂(harmonicEmpirical N x : Measure X)) = harmonicMean (N+1) (fun n => F (x n)) := by
  change (∫ y, F y ∂harmonicEmpiricalRaw N x) = _
  rw [harmonicEmpiricalRaw,integral_finset_sum_measure]
  · simp only [integral_smul_measure,integral_dirac,smul_eq_mul]
    rw [harmonicMean,sum_div]
    apply sum_congr rfl
    intro n hn
    rw [ENNReal.toReal_ofReal (harmonicWeight_nonneg N n),harmonicWeight]
    ring
  · intro n hn
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- Compactness supplies one subsequence for all continuous tests at once. -/
theorem exists_harmonicEmpirical_limit [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] [MetrizableSpace X] [SeparableSpace X]
    (x : ℕ → X) (D : ℕ → ℕ) :
    ∃ μ : ProbabilityMeasure X, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => harmonicEmpirical (D (φ j)) x) atTop (𝓝 μ) := by
  obtain ⟨μ,_,φ,hφ,hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun j => harmonicEmpirical (D j) x) (fun j => Set.mem_univ _)
  exact ⟨μ,φ,hφ,hlim⟩

#print axioms integral_harmonicEmpirical
#print axioms exists_harmonicEmpirical_limit
end Erdos371.FiniteInformation
