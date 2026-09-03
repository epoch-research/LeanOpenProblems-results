import Submission.RichSlopes

/-!
Quantitative positive-measure sets of slopes with many genuine prime pairs.
The lower bound on their measure decreases with the cutoff, so it does not by itself
prove infinitely many pairs at a fixed slope.
-/
namespace Erdos972MetricRichness

open Finset MeasureTheory Filter
open Erdos972ChebyshevLower Erdos972RichSlopes

lemma weightedPairs_le_theta {N : ℕ} (hN : 2 ≤ N) (α : ℝ) :
    weightedPairs N α ≤ Chebyshev.theta N * Real.log (8 * N) := by
  classical
  have hN2 : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hlog8N : 0 ≤ Real.log (8 * N) := Real.log_nonneg (by linarith)
  unfold weightedPairs
  rw [Chebyshev.theta, Nat.floor_natCast, sum_mul]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpN, hp⟩ := mem_filter.mp hp
  have hpp := hp
  have hpN' := (mem_Ioc.mp hpN).2
  have hb := inner_sum_le (α := α) hp.two_le hp (le_refl p)
  by_cases hq : (⌊α * p⌋₊).Prime
  · rw [if_pos hq] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hp.one_le))
    apply Real.log_le_log (mul_pos (by norm_num) (Nat.cast_pos.mpr hp.pos))
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpN') (by norm_num)
  · rw [if_neg hq] at hb
    exact hb.trans (mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) hlog8N)

lemma weightedPairs_uniform_upper {N : ℕ} (hN : 2 ≤ N) (α : ℝ) :
    weightedPairs N α ≤ Real.log 4 * N * Real.log (8 * N) := by
  apply (weightedPairs_le_theta hN α).trans
  apply mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N))
  apply Real.log_nonneg
  have : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
  linarith

lemma measurable_weightedPairs (N : ℕ) : Measurable (weightedPairs N) := by
  classical
  unfold weightedPairs pairBox
  fun_prop (disch := exact measurableSet_Ico)

lemma measurableSet_irrational : MeasurableSet {α : ℝ | Irrational α} := by
  exact (Set.countable_range (fun r : ℚ => (r : ℝ))).measurableSet.compl

noncomputable def threshold (N : ℕ) : ℝ := Real.log 2 ^ 2 * N / 32

noncomputable def weightedRich (N : ℕ) : Set ℝ :=
  Set.Ioo (1 : ℝ) 9 ∩ {α | Irrational α} ∩ {α | threshold N < weightedPairs N α}

lemma measurableSet_weightedRich (N : ℕ) : MeasurableSet (weightedRich N) :=
  (measurableSet_Ioo.inter measurableSet_irrational).inter
    (measurableSet_lt measurable_const (measurable_weightedPairs N))

lemma weightedRich_subset (N : ℕ) : weightedRich N ⊆ Set.Ioo (1 : ℝ) 9 :=
  fun _ h => h.1.1

lemma weightedRich_measure_ne_top (N : ℕ) : volume (weightedRich N) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show volume (Set.Ioo (1 : ℝ) 9) ≠ ⊤ by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact measure_mono (weightedRich_subset N)

lemma integral_le_threshold_add_rich {N : ℕ} (hN : 2 ≤ N) :
    (∫ α : ℝ, weightedPairs N α) ≤
      8 * threshold N + volume.real (weightedRich N) *
        (Real.log 4 * N * Real.log (8 * N)) := by
  let U : ℝ := Real.log 4 * N * Real.log (8 * N)
  let f : ℝ → ℝ := (Set.Ioo (1 : ℝ) 9).indicator (fun _ => threshold N)
  let g : ℝ → ℝ := (weightedRich N).indicator (fun _ => U)
  have ht : 0 ≤ threshold N := by unfold threshold; positivity
  have hf : Integrable f :=
    (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Ioo
  have hg : Integrable g :=
    (integrableOn_const (weightedRich_measure_ne_top N)).integrable_indicator
      (measurableSet_weightedRich N)
  have hb : (fun α => weightedPairs N α) ≤ᵐ[volume] (fun α => f α + g α) := by
    filter_upwards [ae_irrational] with α hI
    by_cases hm : α ∈ Set.Ioo (1 : ℝ) 9
    · have hfα : f α = threshold N := Set.indicator_of_mem hm _
      rw [hfα]
      by_cases he : α ∈ weightedRich N
      · have hgα : g α = U := Set.indicator_of_mem he _
        rw [hgα]
        have hu := weightedPairs_uniform_upper hN α
        change weightedPairs N α ≤ U at hu
        linarith
      · have hgα : g α = 0 := Set.indicator_of_notMem he _
        rw [hgα, add_zero]
        apply le_of_not_gt
        intro hbig
        exact he ⟨⟨hm, hI⟩, hbig⟩
    · have he : α ∉ weightedRich N := fun h => hm (weightedRich_subset N h)
      rw [weightedPairs_eq_zero_of_not_mem N hm,
        show f α = 0 from Set.indicator_of_notMem hm _,
        show g α = 0 from Set.indicator_of_notMem he _]
      norm_num
  have hi := integral_mono_ae (integrable_weightedPairs N) (hf.add hg) hb
  change (∫ α : ℝ, weightedPairs N α) ≤ (∫ α : ℝ, f α + g α) at hi
  rw [integral_add hf hg] at hi
  dsimp [f, g] at hi
  rw [integral_indicator_const _ measurableSet_Ioo,
    integral_indicator_const _ (measurableSet_weightedRich N), Real.volume_real_Ioo] at hi
  norm_num only [show (9 : ℝ) - 1 = 8 by norm_num,
    max_eq_left (by norm_num : (0 : ℝ) ≤ 8), smul_eq_mul] at hi
  exact hi

lemma weightedRich_measure_lower {N : ℕ} (hN : 2 ≤ N)
    (hlower : (Real.log 2 ^ 2 / 2) * N ≤ ∫ α : ℝ, weightedPairs N α) :
    Real.log 2 / (8 * Real.log (8 * N)) ≤ volume.real (weightedRich N) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlog8 : 0 < Real.log (8 * N) := Real.log_pos (by
    have : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
    linarith)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hU : 0 < Real.log 4 * N * Real.log (8 * N) := by
    rw [hlog4]
    positivity
  have hu := integral_le_threshold_add_rich hN
  unfold threshold at hu
  have hcore : Real.log 2 ^ 2 * N / 4 ≤ volume.real (weightedRich N) *
      (Real.log 4 * N * Real.log (8 * N)) := by linarith
  have hdiv := (div_le_iff₀ hU).mpr hcore
  have he : (Real.log 2 ^ 2 * N / 4) / (Real.log 4 * N * Real.log (8 * N)) =
      Real.log 2 / (8 * Real.log (8 * N)) := by
    rw [hlog4]
    field_simp; ring
  rwa [he] at hdiv

/-- Slopes at which the actual prime-input count exceeds a fixed constant times
`N / (log N * log (8*N))`. -/
noncomputable def manyPairSlopes (N : ℕ) : Set ℝ :=
  {α | 1 < α ∧ α < 9 ∧ Irrational α ∧
    threshold N / (Real.log N * Real.log (8 * N)) < (pairInputs N α).card}

lemma weightedRich_subset_manyPairSlopes {N : ℕ} (hN : 2 ≤ N) :
    weightedRich N ⊆ manyPairSlopes N := by
  intro α hα
  obtain ⟨⟨hm, hI⟩, hbig⟩ := hα
  refine ⟨hm.1, hm.2, hI, ?_⟩
  have hN2 : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hlogs : 0 < Real.log N * Real.log (8 * N) := by
    apply mul_pos <;> apply Real.log_pos <;> linarith
  apply (div_lt_iff₀ hlogs).mpr
  exact hbig.trans_le (weightedPairs_le_card hN α)

/-- A quantitative measure lower bound for genuine two-prime configurations.
Its right-hand side tends to zero, so this is not an almost-everywhere or a
pointwise infinitude theorem. -/
theorem eventually_manyPairSlopes_measure_lower :
    ∀ᶠ N : ℕ in atTop,
      Real.log 2 / (8 * Real.log (8 * N)) ≤ volume.real (manyPairSlopes N) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_integral_weightedPairs_lower]
    with N hN hlower
  apply (weightedRich_measure_lower hN hlower).trans
  apply measureReal_mono (weightedRich_subset_manyPairSlopes hN) (h₂ := ?_)
  apply ne_top_of_le_ne_top (show volume (Set.Ioo (1 : ℝ) 9) ≠ ⊤ by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  exact measure_mono (show manyPairSlopes N ⊆ Set.Ioo (1 : ℝ) 9 from
    fun α hα => ⟨hα.1, hα.2.1⟩)

#print axioms weightedPairs_uniform_upper
#print axioms eventually_manyPairSlopes_measure_lower

end Erdos972MetricRichness
