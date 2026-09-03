import Submission.FirstHitSaturatedMedium
import Submission.FirstHitSaturatedEarly
import Submission.FirstHitMainSum
import Submission.EulerMassNineFifths

/-! First-hit main term at the cutoff exp(25 L / 54), using cubic saturation in the early range. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter

lemma saturatedHit_initial_split (L : ℝ) (hL : 0 ≤ L) (f : ℕ → ℝ) :
    (∑ p ∈ (saturatedHitPrimeCut L 0 + 1).primesBelow, f p) =
      (∑ p ∈ saturatedHitMediumPrimes L, f p) +
        ∑ p ∈ (saturatedHitPrimeCut L 24 + 1).primesBelow, f p := by
  have ha := saturatedHitPrimeCut_antitone L hL (by omega : 0 ≤ 24)
  have hsub : (saturatedHitPrimeCut L 24 + 1).primesBelow ⊆ (saturatedHitPrimeCut L 0 + 1).primesBelow := by
    intro p hp
    obtain ⟨hpp, hplo⟩ := WeightedMertens.mem_primes.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨hpp, hplo.trans ha⟩
  have he : ((saturatedHitPrimeCut L 0 + 1).primesBelow \ (saturatedHitPrimeCut L 24 + 1).primesBelow : Finset ℕ) =
      saturatedHitMediumPrimes L := by
    ext p
    simp only [saturatedHitMediumPrimes, Finset.mem_sdiff, mem_filter, mem_Ioc, WeightedMertens.mem_primes]
    constructor
    · rintro ⟨⟨hpp, hpt⟩, hn⟩
      refine ⟨⟨?_, hpt⟩, hpp⟩
      by_contra h
      exact hn ⟨hpp, by omega⟩
    · rintro ⟨⟨hlo, hhi⟩, hpp⟩
      exact ⟨⟨hpp, hhi⟩, fun hh => (not_le_of_gt hlo) hh.2⟩
  have hh := sum_sdiff (f := f) hsub
  rw [he] at hh
  exact hh.symm

noncomputable def saturatedHitMainMargin : ℝ := 6 / 5 - (109 / 100) - saturatedEarlyMain
noncomputable def saturatedHitTotalError : ℝ := saturatedHitChordError + saturatedEarlyError

lemma saturatedHitMainMargin_gt : (6 / 1000 : ℝ) < saturatedHitMainMargin := by norm_num [saturatedHitMainMargin, saturatedEarlyMain]

lemma saturatedHitTotalError_nonneg : 0 ≤ saturatedHitTotalError := by
  unfold saturatedHitTotalError saturatedHitChordError
  have hC := WeightedMertens.boundConstant_pos
  have hM := saturatedEarlyError_nonneg
  have hsum : 0 ≤ ∑ j ∈ range 24,
      (2 * |saturatedHitExcessIntercept j - saturatedHitExcessSlope j / 2| * (2 * saturatedHitNode (j + 1) + 1) ^ 2 +
        |saturatedHitExcessSlope j| * (2 * saturatedHitNode (j + 1) + 1) ^ 3) := by
    apply sum_nonneg
    intro j hj
    have hn : 0 ≤ 2 * saturatedHitNode (j + 1) + 1 := by
      have hh := (saturatedHitNode_mem (j + 1) (by have := mem_range.mp hj; omega)).1
      linarith
    positivity
  positivity


noncomputable def saturatedHitMainSum (L : ℝ) : ℝ :=
  ∑ p ∈ (saturatedHitPrimeCut L 0 + 1).primesBelow,
    (1 / (p : ℝ)) / primeNormalizer p.primesBelow (firstHitCutoff L p)

/-- All finite main-term estimates combined. The fixed small wheel, the
large-prime thresholds, and the Euler-product upper bound are explicit. -/
theorem saturatedHitMainSum_finite_bound (L : ℝ) (hL : 0 < L) (hsmall : 9 * log 2 ≤ L)
    (W : ℕ) (hW : 0 < W) (hWF : W ≤ firstHitFarCut L)
    (hWheel : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L)
    (hthreshold : ∀ p, p.Prime → W < p → FirstHitLogThresholds p)
    (hEuler : ∀ R : ℕ, W ≤ R → eulerMass (R + 1).primesBelow ≤ (9 / 5 : ℝ) * log (R : ℝ)) :
    saturatedHitMainSum L ≤ 1 - saturatedHitMainMargin / L + saturatedHitTotalError / L ^ 2 := by
  let R := saturatedHitPrimeCut L 24
  let Z := saturatedHitPrimeCut L 0
  have hWR : W ≤ saturatedHitPrimeCut L 24 := by
    change W ≤ firstHitPrimeCut L 23
    exact hWF.trans (firstHitFarCut_le_cubeCut L hL.le)
  have hR : 0 < R := lt_of_lt_of_le hW hWR
  have hRZ : R ≤ Z := saturatedHitPrimeCut_antitone L hL.le (by omega : 0 ≤ 24)
  have hZ : 0 < Z := hR.trans_le hRZ
  have hZL : log (Z : ℝ) ≤ 25 * L / 54 := by
    have hh := log_le_log (show (0 : ℝ) < Z by exact_mod_cast hZ)
      (Nat.floor_le (exp_pos (L / (2 * saturatedHitNode 0 + 1))).le)
    rw [log_exp] at hh
    norm_num [saturatedHitNode, firstHitNode] at hh
    linarith
  have hearly := firstHit_saturated_early_sum_bound L hL hsmall W hW hWF hWheel hthreshold hEuler
  have hmidmem (p : ℕ) (hp : p ∈ saturatedHitMediumPrimes L) : p.Prime ∧ W < p := by
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    exact ⟨hpp, hWR.trans_lt (mem_Ioc.mp hpI).1⟩
  have hmedium := saturatedHit_medium_sum_le L hL (by have := log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith)
    (fun p hp => (hthreshold p (hmidmem p hp).1 (hmidmem p hp).2).2.2)
    (fun p hp => hEuler p (hmidmem p hp).2.le)
  have hextotal : (∑ p ∈ (Z + 1).primesBelow, firstHitMeanExcess L p) ≤
      (109 / 100) / L + saturatedHitChordError / L ^ 2 +
        (saturatedEarlyMain / L + saturatedEarlyError / L ^ 2) := by
    rw [saturatedHit_initial_split L hL.le]
    exact add_le_add hmedium hearly
  have hE : eulerMass (Z + 1).primesBelow ≤ (5 / 6 : ℝ) * L := by
    have hh := hEuler Z (hWR.trans hRZ)
    linarith
  have hEinv : 6 / (5 * L) ≤ 1 / eulerMass (Z + 1).primesBelow := by
    have hh := one_div_le_one_div_of_le
      (eulerMass_pos (Z + 1).primesBelow (fun p hp => (WeightedMertens.mem_primes.mp hp).1)) hE
    convert hh using 1 <;> ring
  have hid : saturatedHitMainSum L = (∑ p ∈ (Z + 1).primesBelow, firstHitMeanExcess L p) +
      (1 - 1 / eulerMass (Z + 1).primesBelow) := by
    rw [← initial_density_telescope Z, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    unfold firstHitMeanExcess
    ring
  rw [hid]
  unfold saturatedHitMainMargin saturatedHitTotalError
  linear_combination hextotal + hEinv

lemma saturatedHitMainSum_slack_of_finite_bound (L : ℝ) (hL : 0 < L)
    (herror : 1000 * saturatedHitTotalError ≤ L)
    (hmain : saturatedHitMainSum L ≤ 1 - saturatedHitMainMargin / L + saturatedHitTotalError / L ^ 2) :
    saturatedHitMainSum L ≤ 1 - 1 / (200 * L) := by
  have herr : saturatedHitTotalError / L ^ 2 ≤ 1 / (1000 * L) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL) (by positivity)).mpr
    nlinarith only [mul_nonneg hL.le (show 0 ≤ L - 1000 * saturatedHitTotalError by linarith)]
  have hmargin := div_le_div_of_nonneg_right saturatedHitMainMargin_gt.le hL.le
  linear_combination hmain + herr + hmargin

lemma exists_saturatedHit_threshold_wheel : ∃ W : ℕ, 2 ≤ W ∧
    (∀ p, p.Prime → W < p → FirstHitLogThresholds p) ∧
    (∀ R : ℕ, W ≤ R → eulerMass (R + 1).primesBelow ≤ (9 / 5 : ℝ) * log (R : ℝ)) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_eulerMass_initial_le_nine_fifths_log
  let H : ℝ := max (50 * WeightedMertens.sharpMomentError)
    (max supportMassLogThreshold (20000 * firstHitProfileError))
  obtain ⟨N, hN⟩ := exists_nat_ge (exp H)
  let W : ℕ := max N (max M 2)
  have hNW : N ≤ W := le_max_left _ _
  have hMW : M ≤ W := (le_max_left M 2).trans (le_max_right N _)
  have hW2 : 2 ≤ W := (le_max_right M 2).trans (le_max_right N _)
  refine ⟨W, hW2, ?_, fun R hR => hM R (hMW.trans hR)⟩
  intro p hp hpW
  have hNp : N ≤ p := hNW.trans hpW.le
  have hh := log_le_log (exp_pos H) (hN.trans (show (N : ℝ) ≤ p by exact_mod_cast hNp))
  rw [log_exp] at hh
  unfold FirstHitLogThresholds
  exact ⟨(le_max_left _ _).trans hh,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hh,
    ((le_max_right _ _).trans (le_max_right _ _)).trans hh⟩

/-- An unconditional main-term margin for the variable-cutoff first-hit
Selberg construction. Coefficient costs and transfer to a Jacobsthal bound
are separate obligations. -/
theorem exists_saturatedHitMainSum_slack : ∃ L₀ : ℝ, 0 < L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → saturatedHitMainSum L ≤ 1 - 1 / (200 * L) := by
  obtain ⟨W, hW2, hthreshold, hEuler⟩ := exists_saturatedHit_threshold_wheel
  have hW : 0 < W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hlogW : 0 ≤ log (W : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ W by omega))
  have hlogQ : 0 ≤ log (firstHitWheel W : ℝ) :=
    log_nonneg (by exact_mod_cast firstHitWheel_pos W)
  have hlogW2 : 0 ≤ log ((W : ℝ) + 2) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) W; linarith)
  let L₀ : ℝ := 1 + 9 * log ((W : ℝ) + 2) +
    2 * log (firstHitWheel W : ℝ) + log (W : ℝ) + 1000 * saturatedHitTotalError
  have hL₀ : 0 < L₀ := by dsimp [L₀]; nlinarith [saturatedHitTotalError_nonneg]
  refine ⟨L₀, hL₀, ?_⟩
  intro L hLL
  have hL : 0 < L := hL₀.trans_le hLL
  have hlarge : 9 * log ((W : ℝ) + 2) ≤ L := by dsimp [L₀] at hLL; nlinarith [saturatedHitTotalError_nonneg]
  have hWheel : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L := by
    dsimp [L₀] at hLL
    nlinarith [saturatedHitTotalError_nonneg]
  have herror : 1000 * saturatedHitTotalError ≤ L := by dsimp [L₀] at hLL; nlinarith
  have hsmall : 9 * log (2 : ℝ) ≤ L := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (W : ℝ) + 2 by have := Nat.cast_nonneg (α := ℝ) W; linarith)
    linarith
  have hWF : W ≤ firstHitFarCut L := by
    have hwlog := log_le_log hW0 (show (W : ℝ) ≤ (W : ℝ) + 2 by linarith)
    have hh : (W : ℝ) ≤ exp (L / 9) := by
      calc
        (W : ℝ) = exp (log (W : ℝ)) := (exp_log hW0).symm
        _ ≤ exp (L / 9) := exp_le_exp.mpr (by linarith)
    exact Nat.le_floor hh
  exact saturatedHitMainSum_slack_of_finite_bound L hL herror
    (saturatedHitMainSum_finite_bound L hL hsmall W hW hWF hWheel hthreshold hEuler)

#print axioms saturatedHitMainSum_finite_bound
#print axioms exists_saturatedHitMainSum_slack
end Erdos970.FiniteSelberg
