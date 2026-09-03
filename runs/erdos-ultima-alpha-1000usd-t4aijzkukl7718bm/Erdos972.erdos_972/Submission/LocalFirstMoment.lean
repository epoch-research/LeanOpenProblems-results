import Submission.ChebyshevPNT
import Submission.MetricInfinitePairs

/-! A lower first moment localized to any fixed slope interval inside `(1,8)`. -/
namespace Erdos972LocalFirstMoment

open Finset MeasureTheory Filter
open Erdos972ChebyshevLower Erdos972RichSlopes Erdos972MetricRichness
open Erdos972MetricInfinitePairs Erdos972ChebyshevPNT

lemma theta_sub_real {x y : ℝ} (hxy : x ≤ y) :
    Chebyshev.theta y - Chebyshev.theta x =
      ∑ q ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log q := by
  have h := theta_sub_eq_sum (Nat.floor_mono hxy)
  simpa only [Chebyshev.theta, Nat.floor_natCast] using h

lemma setIntegral_pairBox_nonneg (a b : ℝ) (p q : ℕ) :
    0 ≤ ∫ α in Set.Ioo a b, pairBox p q α := by
  apply integral_nonneg
  intro α
  apply Set.indicator_nonneg
  intro _ _
  exact mul_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)

lemma setIntegral_pairBox_eq {a b : ℝ} {p q : ℕ} (hp : 0 < p)
    (hlo : a * p < q) (hhi : (q : ℝ) + 1 < b * p) :
    (∫ α in Set.Ioo a b, pairBox p q α) = Real.log p * Real.log q / p := by
  rw [← integral_pairBox hp q]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro α hα
  apply Set.indicator_of_notMem
  intro hmem
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have h₁ := (div_le_iff₀ hpR).mp hmem.1
  have h₂ := (lt_div_iff₀ hpR).mp hmem.2
  apply hα
  exact ⟨(mul_lt_mul_iff_left₀ hpR).mp (hlo.trans_le h₁),
    (mul_lt_mul_iff_left₀ hpR).mp (h₂.trans hhi)⟩

lemma inner_local_lower {a b c d : ℝ} (ha : 1 < a) (hac : a < c)
    (hcd : c < d) (hdb : d < b) (hb : b < 8) {p : ℕ} (hp : 0 < p)
    (hmargin : 1 < (b - d) * p) :
    (Real.log p / p) * (Chebyshev.theta (d * p) - Chebyshev.theta (c * p)) ≤
      ∑ q ∈ (Ioc p (8 * p)).filter Nat.Prime, ∫ α in Set.Ioo a b, pairBox p q α := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hcp0 : 0 ≤ c * p := mul_nonneg (by linarith) hpR.le
  have hdp0 : 0 ≤ d * p := mul_nonneg (by linarith) hpR.le
  have hsub : (Ioc ⌊c * p⌋₊ ⌊d * p⌋₊).filter Nat.Prime ⊆ (Ioc p (8 * p)).filter Nat.Prime := by
    intro q hq
    obtain ⟨hqI, hqprime⟩ := mem_filter.mp hq
    obtain ⟨hql, hqu⟩ := mem_Ioc.mp hqI
    have hqlR : c * p < q := (Nat.floor_lt hcp0).mp hql
    have hquR : (q : ℝ) ≤ d * p := (Nat.le_floor_iff hdp0).mp hqu
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, hqprime⟩
    · have hh : (p : ℝ) < q := by nlinarith
      exact_mod_cast hh
    · have hh : (q : ℝ) ≤ 8 * p := by nlinarith
      exact_mod_cast hh
  rw [theta_sub_real (mul_le_mul_of_nonneg_right hcd.le hpR.le), mul_sum]
  calc
    _ = ∑ q ∈ (Ioc ⌊c * p⌋₊ ⌊d * p⌋₊).filter Nat.Prime,
        ∫ α in Set.Ioo a b, pairBox p q α := by
      apply sum_congr rfl
      intro q hq
      have hqI := mem_Ioc.mp (mem_filter.mp hq).1
      have hqlR : c * p < q := (Nat.floor_lt hcp0).mp hqI.1
      have hquR : (q : ℝ) ≤ d * p := (Nat.le_floor_iff hdp0).mp hqI.2
      rw [setIntegral_pairBox_eq hp (by nlinarith) (by nlinarith)]
      ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => setIntegral_pairBox_nonneg a b p q)

lemma eventually_inner_local_lower {a b : ℝ} (ha : 1 < a) (hab : a < b) (hb : b < 8) :
    ∀ᶠ p : ℕ in atTop, (b - a) / 4 * Real.log p ≤
      ∑ q ∈ (Ioc p (8 * p)).filter Nat.Prime, ∫ α in Set.Ioo a b, pairBox p q α := by
  let c : ℝ := (3 * a + b) / 4
  let d : ℝ := (a + 3 * b) / 4
  have hac : a < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  have hdb : d < b := by dsimp [d]; linarith
  have hc : 0 < c := by linarith
  have hd : 0 < b - d := by linarith
  have htheta := tendsto_natCast_atTop_atTop.eventually (eventually_theta_interval_lower hc hcd)
  have hlarge := tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 / (b - d)))
  filter_upwards [htheta, hlarge, eventually_ge_atTop (1 : ℕ)] with p hpθ hpbig hp1
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hm : 1 < (b - d) * p := by
    have ht := (div_lt_iff₀ hd).mp hpbig
    nlinarith
  apply le_trans _ (inner_local_lower ha hac hcd hdb hb (by omega) hm)
  have hlog : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) hpR.le
  have h := mul_le_mul_of_nonneg_left hpθ hlog
  have he : (Real.log p / p) * ((d - c) / 2 * p) = (b - a) / 4 * Real.log p := by
    dsimp [c, d]
    field_simp
    ring
  rwa [he] at h

lemma eventually_theta_sub_const_lower (P : ℕ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) / 2 ≤ Chebyshev.theta N - Chebyshev.theta P := by
  have hθ := theta_div_self_tendsto.comp tendsto_natCast_atTop_atTop
  have hc := tendsto_const_div_atTop_nhds_zero_nat (Chebyshev.theta P)
  have ht : Tendsto (fun N : ℕ => (Chebyshev.theta N - Chebyshev.theta P) / N) atTop (nhds 1) := by
    simpa only [Function.comp_def, ← sub_div, sub_zero] using hθ.sub hc
  have h := (tendsto_order.mp ht).1 (1 / 2) (by norm_num)
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have ht := (lt_div_iff₀ hN0).mp hN
  linarith

/-- Linear first-moment mass on every fixed interior slope interval. -/
theorem eventually_setIntegral_weightedPairs_lower {a b : ℝ}
    (ha : 1 < a) (hab : a < b) (hb : b < 8) :
    ∀ᶠ N : ℕ in atTop, (b - a) / 8 * N ≤ ∫ α in Set.Ioo a b, weightedPairs N α := by
  obtain ⟨P, hP⟩ := eventually_atTop.mp (eventually_inner_local_lower ha hab hb)
  filter_upwards [eventually_ge_atTop P, eventually_theta_sub_const_lower P] with N hNP hθ
  have hsum : (b - a) / 4 * (Chebyshev.theta N - Chebyshev.theta P) ≤
      ∫ α in Set.Ioo a b, weightedPairs N α := by
    rw [theta_sub_eq_sum hNP, mul_sum]
    unfold weightedPairs
    rw [integral_finset_sum _ (fun p _ =>
      (integrable_finset_sum _ (fun q _ => integrable_pairBox p q)).integrableOn)]
    calc
      _ ≤ ∑ p ∈ (Ioc P N).filter Nat.Prime,
          ∑ q ∈ (Ioc p (8 * p)).filter Nat.Prime, ∫ α in Set.Ioo a b, pairBox p q α := by
        apply sum_le_sum
        intro p hp
        exact hP p (by have := (mem_Ioc.mp (mem_filter.mp hp).1).1; omega)
      _ ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime,
          ∑ q ∈ (Ioc p (8 * p)).filter Nat.Prime, ∫ α in Set.Ioo a b, pairBox p q α := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le P) (mem_Ioc.mp hpI).1,
            (mem_Ioc.mp hpI).2⟩, hpp⟩
        · intro p _ _
          exact sum_nonneg (fun q _ => setIntegral_pairBox_nonneg a b p q)
      _ = _ := by
        apply sum_congr rfl
        intro p _
        exact (integral_finset_sum _ (fun q _ => (integrable_pairBox p q).integrableOn)).symm
  have h := mul_le_mul_of_nonneg_left hθ (show 0 ≤ (b - a) / 4 by linarith)
  nlinarith

#print axioms eventually_setIntegral_weightedPairs_lower

end Erdos972LocalFirstMoment
