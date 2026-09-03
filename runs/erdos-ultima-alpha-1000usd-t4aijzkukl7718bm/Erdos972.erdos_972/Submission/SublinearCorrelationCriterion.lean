import Submission.CorrelationVaughan

/-!
Finite certificates and a weaker sufficient growth condition for prime-pair
infinitude. No correlation lower bound is asserted in this file.
-/
namespace Erdos972SublinearCorrelationCriterion

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972CorrelationVaughan Erdos972Topology

lemma primeCorrelation_le_of_no_new_pairs {α : ℝ} {B N : ℕ}
    (hno : ∀ p : ℕ, p ≤ N → p.Prime → (floorMul α p).Prime → p ≤ B) :
    primeCorrelation α N ≤ primeCorrelation α B := by
  classical
  unfold primeCorrelation
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hpp, hqp⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1,
      hno p (mem_Ioc.mp hpI).2 hpp hqp⟩, hpp, hqp⟩
  · intro p _ _
    exact mul_nonneg (Real.log_natCast_nonneg p)
      (Real.log_natCast_nonneg (floorMul α p))

/-- An exact finite certificate. The displayed strict lower bound is a
hypothesis; this theorem does not supply it for irrational slopes. -/
theorem prime_pair_beyond_of_correlation {α : ℝ} (hα : 1 ≤ α) {B N : ℕ}
    (hN : 1 ≤ N)
    (hlarge : primePowerBudget α N + primeCorrelation α B < mangoldtCorrelation α N) :
    ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧ (floorMul α p).Prime := by
  by_contra hn
  have hno : ∀ p : ℕ, p ≤ N → p.Prime → (floorMul α p).Prime → p ≤ B := by
    intro p hpN hp hq
    exact le_of_not_gt (fun hBp => hn ⟨p, hBp, hpN, hp, hq⟩)
  have hp := primeCorrelation_le_of_no_new_pairs hno
  have he := (prime_power_error_bound_sharp hα hN).2
  change mangoldtCorrelation α N - primeCorrelation α N ≤ primePowerBudget α N at he
  linarith

lemma primeCorrelation_explicit_upper {α : ℝ} (hα : 1 ≤ α) (B : ℕ) :
    primeCorrelation α B ≤ (B : ℝ) * Real.log B * Real.log (α * B) := by
  classical
  by_cases hB : B = 0
  · simp [hB, primeCorrelation]
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hBR
  have hlogαB : 0 ≤ Real.log (α * B) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le hα hBR)
  unfold primeCorrelation
  calc
    _ ≤ ∑ p ∈ (Ioc 0 B).filter (fun p => p.Prime ∧ (floorMul α p).Prime),
        Real.log B * Real.log (α * B) := by
      apply sum_le_sum
      intro p hp
      have hpI := (mem_filter.mp hp).1
      exact mul_le_mul (log_input_le hpI) (log_floorMul_le hα hpI)
        (Real.log_natCast_nonneg _) hlogB
    _ ≤ ∑ p ∈ Ioc 0 B, Real.log B * Real.log (α * B) := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => mul_nonneg hlogB hlogαB)
    _ = _ := by simp [mul_assoc]

/-- A finite certificate using only the explicit prime-power error and the
input cutoff, without computing the prime-pair sum below that cutoff. -/
theorem prime_pair_beyond_of_explicit_correlation {α : ℝ} (hα : 1 ≤ α) {B N : ℕ}
    (hN : 1 ≤ N)
    (hlarge : primePowerBudget α N + (B : ℝ) * Real.log B * Real.log (α * B) <
      mangoldtCorrelation α N) :
    ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧ (floorMul α p).Prime := by
  apply prime_pair_beyond_of_correlation hα hN
  have hb := primeCorrelation_explicit_upper hα B
  linarith

/-- Unbounded excess over the explicit prime-power envelope suffices. This is
weaker than a positive linear lower bound, but remains an unproved analytic
hypothesis when applied to an arbitrary irrational slope. -/
theorem infinite_primeSet_of_unbounded_excess {α : ℝ} (hα : 1 ≤ α)
    (hlarge : ∀ C : ℝ, ∃ N : ℕ, 1 ≤ N ∧
      C < mangoldtCorrelation α N - primePowerBudget α N) :
    (primeSet α).Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro B
  obtain ⟨N, hN, hlargeN⟩ := hlarge (primeCorrelation α B)
  obtain ⟨p, hBp, _, hp, hq⟩ := prime_pair_beyond_of_correlation hα hN
    (show primePowerBudget α N + primeCorrelation α B < mangoldtCorrelation α N by linarith)
  exact ⟨p, ⟨hp, hq⟩, hBp⟩

/-- A hypothetical finite prime-pair set bounds the excess at every positive
scale, not only after normalization by the scale. -/
theorem finite_primeSet_bounds_excess {α : ℝ} (hα : 1 ≤ α)
    (hfin : (primeSet α).Finite) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      mangoldtCorrelation α N - primePowerBudget α N ≤ C := by
  obtain ⟨C, hC⟩ := primeCorrelation_bounded_of_finite hfin
  refine ⟨C, fun N hN => ?_⟩
  have he := (prime_power_error_bound_sharp hα hN).2
  change mangoldtCorrelation α N - primeCorrelation α N ≤ primePowerBudget α N at he
  linarith [hC N]

#print axioms prime_pair_beyond_of_explicit_correlation
#print axioms infinite_primeSet_of_unbounded_excess
#print axioms finite_primeSet_bounds_excess

/-- The prime-power contribution is negligible relative to every power
strictly greater than the square-root scale. -/
lemma primePowerBudget_div_rpow_tendsto {α s : ℝ} (hα : 1 ≤ α) (hs : 1 / 2 < s) :
    Tendsto (fun N : ℕ => primePowerBudget α N / (N : ℝ)^s) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hd : 0 < s - 1 / 2 := by linarith
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^(s - 1 / 2)) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log α / (N : ℝ)^(s - 1 / 2))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hpow
  have hl : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)^(s - 1 / 2))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (Real.log 4 + 12) *
      (Real.log α / (N : ℝ)^(s - 1 / 2) +
        (1 + Real.sqrt α) * (Real.log N / (N : ℝ)^(s - 1 / 2)))) atTop (𝓝 0) := by
    simpa using (hc.add (hl.const_mul (1 + Real.sqrt α))).const_mul (Real.log 4 + 12)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hpd : 0 < (N : ℝ)^(s - 1 / 2) := Real.rpow_pos_of_pos hNR _
  have hm : Real.sqrt N * (N : ℝ)^(s - 1 / 2) = (N : ℝ)^s := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNR]
    congr 1
    ring
  unfold primePowerBudget
  rw [Real.log_mul hα0.ne' hNR.ne', Real.sqrt_mul hα0.le, ← hm]
  field_simp [hsqrt.ne', hpd.ne']
  ring

/-- Finitude forces a stronger necessary condition than merely `o(N)`:
the correlation is `o(N^s)` for every `s > 1/2`. -/
theorem finite_primeSet_correlation_div_rpow_tendsto_zero {α s : ℝ}
    (hα : 1 ≤ α) (hs : 1 / 2 < s) (hfin : (primeSet α).Finite) :
    Tendsto (fun N : ℕ => mangoldtCorrelation α N / (N : ℝ)^s) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := primeCorrelation_bounded_of_finite hfin
  have hs0 : 0 < s := by linarith
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^s) atTop atTop :=
    (tendsto_rpow_atTop hs0).comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => C / (N : ℝ)^s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hlim : Tendsto (fun N : ℕ => C / (N : ℝ)^s +
      primePowerBudget α N / (N : ℝ)^s) atTop (𝓝 0) := by
    simpa using hc.add (primePowerBudget_div_rpow_tendsto hα hs)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [] with N
    apply div_nonneg _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact sum_nonneg (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have he := (prime_power_error_bound_sharp hα hN).2
    change mangoldtCorrelation α N - primeCorrelation α N ≤ primePowerBudget α N at he
    have hh : mangoldtCorrelation α N ≤ C + primePowerBudget α N := by linarith [hC N]
    simpa only [add_div] using div_le_div_of_nonneg_right hh
      (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) N) s)

/-- A positive `N^s` lower bound on arbitrarily large scales is sufficient for
any `s > 1/2`. The lower bound itself remains an explicit hypothesis. -/
theorem infinite_primeSet_of_frequently_rpow_lower {α s c : ℝ}
    (hα : 1 ≤ α) (hs : 1 / 2 < s) (hc : 0 < c)
    (hlarge : ∃ᶠ N : ℕ in atTop, c * (N : ℝ)^s ≤ mangoldtCorrelation α N) :
    (primeSet α).Infinite := by
  intro hfin
  have hlim := finite_primeSet_correlation_div_rpow_tendsto_zero hα hs hfin
  have hevent : ∀ᶠ N : ℕ in atTop, mangoldtCorrelation α N / (N : ℝ)^s < c :=
    (tendsto_order.mp hlim).2 c hc
  obtain ⟨N, hbig, hsmall, hN⟩ :=
    (hlarge.and_eventually (hevent.and (eventually_ge_atTop (1 : ℕ)))).exists
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ)^s := Real.rpow_pos_of_pos hNR s
  exact (not_le_of_gt hsmall) ((le_div_iff₀ hpos).mpr hbig)

#print axioms primePowerBudget_div_rpow_tendsto
#print axioms finite_primeSet_correlation_div_rpow_tendsto_zero
#print axioms infinite_primeSet_of_frequently_rpow_lower

end Erdos972SublinearCorrelationCriterion
