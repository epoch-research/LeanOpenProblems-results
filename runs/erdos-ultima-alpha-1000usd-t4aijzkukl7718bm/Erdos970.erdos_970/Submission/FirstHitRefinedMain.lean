import Submission.FirstHitRefinedMedium
import Submission.FirstHitMainSum
import Submission.EulerMassNineFifths

/-! First-hit main term at the larger cutoff exp(50 L / 113). -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter

lemma refinedHit_initial_split (L : ℝ) (hL : 0 ≤ L) (f : ℕ → ℝ) :
    (∑ p ∈ (refinedHitPrimeCut L 0 + 1).primesBelow, f p) =
      (∑ p ∈ refinedHitMediumPrimes L, f p) +
        ∑ p ∈ (refinedHitPrimeCut L 24 + 1).primesBelow, f p := by
  have ha := refinedHitPrimeCut_antitone L hL (by omega : 0 ≤ 24)
  have hsub : (refinedHitPrimeCut L 24 + 1).primesBelow ⊆ (refinedHitPrimeCut L 0 + 1).primesBelow := by
    intro p hp
    obtain ⟨hpp, hplo⟩ := WeightedMertens.mem_primes.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨hpp, hplo.trans ha⟩
  have he : ((refinedHitPrimeCut L 0 + 1).primesBelow \ (refinedHitPrimeCut L 24 + 1).primesBelow : Finset ℕ) =
      refinedHitMediumPrimes L := by
    ext p
    simp only [refinedHitMediumPrimes, Finset.mem_sdiff, mem_filter, mem_Ioc, WeightedMertens.mem_primes]
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

noncomputable def refinedHitMainMargin : ℝ := 113 / 90 - (35213 / 36000) - 42 / 155
noncomputable def refinedHitTotalError : ℝ := refinedHitChordError + 588 * WeightedMertens.sharpMomentError / 31

lemma refinedHitMainMargin_gt : (6 / 1000 : ℝ) < refinedHitMainMargin := by norm_num [refinedHitMainMargin]

lemma refinedHitTotalError_nonneg : 0 ≤ refinedHitTotalError := by
  unfold refinedHitTotalError refinedHitChordError
  have hC := WeightedMertens.boundConstant_pos
  have hM := WeightedMertens.sharpMomentError_pos
  have hsum : 0 ≤ ∑ j ∈ range 24,
      (2 * |refinedHitExcessIntercept j - refinedHitExcessSlope j / 2| * (2 * refinedHitNode (j + 1) + 1) ^ 2 +
        |refinedHitExcessSlope j| * (2 * refinedHitNode (j + 1) + 1) ^ 3) := by
    apply sum_nonneg
    intro j hj
    have hn : 0 ≤ 2 * refinedHitNode (j + 1) + 1 := by
      have hh := (refinedHitNode_mem (j + 1) (by have := mem_range.mp hj; omega)).1
      linarith
    positivity
  positivity


noncomputable def refinedHitMainSum (L : ℝ) : ℝ :=
  ∑ p ∈ (refinedHitPrimeCut L 0 + 1).primesBelow,
    (1 / (p : ℝ)) / primeNormalizer p.primesBelow (firstHitCutoff L p)

/-- All finite main-term estimates combined. The fixed small wheel, the
large-prime thresholds, and the Euler-product upper bound are explicit. -/
theorem refinedHitMainSum_finite_bound (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L)
    (W : ℕ) (hW : 0 < W) (hWR : W ≤ refinedHitPrimeCut L 24)
    (hWheel : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L)
    (hthreshold : ∀ p, p.Prime → W < p → FirstHitLogThresholds p)
    (hEuler : ∀ R : ℕ, W ≤ R → eulerMass (R + 1).primesBelow ≤ (9 / 5 : ℝ) * log (R : ℝ)) :
    refinedHitMainSum L ≤ 1 - refinedHitMainMargin / L + refinedHitTotalError / L ^ 2 := by
  let R := refinedHitPrimeCut L 24
  let Z := refinedHitPrimeCut L 0
  have hR : 0 < R := lt_of_lt_of_le hW hWR
  have hRZ : R ≤ Z := refinedHitPrimeCut_antitone L hL.le (by omega : 0 ≤ 24)
  have hZ : 0 < Z := hR.trans_le hRZ
  have hRL : 7 * log (R : ℝ) ≤ L := by
    have hh := log_le_log (show (0 : ℝ) < R by exact_mod_cast hR)
      (Nat.floor_le (exp_pos (L / (2 * refinedHitNode 24 + 1))).le)
    rw [log_exp] at hh
    norm_num [refinedHitNode, firstHitNode] at hh
    linarith
  have hZL : log (Z : ℝ) ≤ 50 * L / 113 := by
    have hh := log_le_log (show (0 : ℝ) < Z by exact_mod_cast hZ)
      (Nat.floor_le (exp_pos (L / (2 * refinedHitNode 0 + 1))).le)
    rw [log_exp] at hh
    norm_num [refinedHitNode, firstHitNode] at hh
    linarith
  let P := (R + 1).primesBelow.filter (fun p => W < p)
  have hearly := first_hit_early_sum_bound R hR L hL hRL P (filter_subset _ _)
    (firstHitCutoff L) (fun p _ => firstHitCutoff_pos L p)
    (fun p _ => firstHitCutoff_log_lower L p)
    (fun p hp => (hthreshold p (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1 (mem_filter.mp hp).2).1)
    (fun p hp => (hthreshold p (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1 (mem_filter.mp hp).2).2.1)
  have hpart := sum_filter_add_sum_filter_not (R + 1).primesBelow (fun p => W < p) (firstHitMeanExcess L)
  have hz : (∑ p ∈ (R + 1).primesBelow with ¬W < p, firstHitMeanExcess L p) = 0 := by
    apply sum_eq_zero
    intro p hp
    exact firstHitMeanExcess_zero_on_wheel W hW L hWheel p
      (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1 (by have := (mem_filter.mp hp).2; omega)
  rw [hz, add_zero] at hpart
  change (∑ p ∈ P, firstHitMeanExcess L p) = _ at hpart
  change (∑ p ∈ P, firstHitMeanExcess L p) ≤ _ at hearly
  rw [hpart] at hearly
  have hmidmem (p : ℕ) (hp : p ∈ refinedHitMediumPrimes L) : p.Prime ∧ W < p := by
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    exact ⟨hpp, hWR.trans_lt (mem_Ioc.mp hpI).1⟩
  have hmedium := refinedHit_medium_sum_le L hL hsmall
    (fun p hp => (hthreshold p (hmidmem p hp).1 (hmidmem p hp).2).2.2)
    (fun p hp => hEuler p (hmidmem p hp).2.le)
  have hextotal : (∑ p ∈ (Z + 1).primesBelow, firstHitMeanExcess L p) ≤
      (35213 / 36000) / L + refinedHitChordError / L ^ 2 +
        (42 / (155 * L) + 588 * WeightedMertens.sharpMomentError / (31 * L ^ 2)) := by
    rw [refinedHit_initial_split L hL.le]
    exact add_le_add hmedium hearly
  have hE : eulerMass (Z + 1).primesBelow ≤ (90 / 113 : ℝ) * L := by
    have hh := hEuler Z (hWR.trans hRZ)
    linarith
  have hEinv : 113 / (90 * L) ≤ 1 / eulerMass (Z + 1).primesBelow := by
    have hh := one_div_le_one_div_of_le
      (eulerMass_pos (Z + 1).primesBelow (fun p hp => (WeightedMertens.mem_primes.mp hp).1)) hE
    convert hh using 1 <;> ring
  have hid : refinedHitMainSum L = (∑ p ∈ (Z + 1).primesBelow, firstHitMeanExcess L p) +
      (1 - 1 / eulerMass (Z + 1).primesBelow) := by
    rw [← initial_density_telescope Z, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    unfold firstHitMeanExcess
    ring
  rw [hid]
  unfold refinedHitMainMargin refinedHitTotalError
  linear_combination hextotal + hEinv

lemma refinedHitMainSum_slack_of_finite_bound (L : ℝ) (hL : 0 < L)
    (herror : 1000 * refinedHitTotalError ≤ L)
    (hmain : refinedHitMainSum L ≤ 1 - refinedHitMainMargin / L + refinedHitTotalError / L ^ 2) :
    refinedHitMainSum L ≤ 1 - 1 / (200 * L) := by
  have herr : refinedHitTotalError / L ^ 2 ≤ 1 / (1000 * L) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL) (by positivity)).mpr
    nlinarith only [mul_nonneg hL.le (show 0 ≤ L - 1000 * refinedHitTotalError by linarith)]
  have hmargin := div_le_div_of_nonneg_right refinedHitMainMargin_gt.le hL.le
  linear_combination hmain + herr + hmargin

lemma exists_refinedHit_threshold_wheel : ∃ W : ℕ, 2 ≤ W ∧
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
theorem exists_refinedHitMainSum_slack : ∃ L₀ : ℝ, 0 < L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → refinedHitMainSum L ≤ 1 - 1 / (200 * L) := by
  obtain ⟨W, hW2, hthreshold, hEuler⟩ := exists_refinedHit_threshold_wheel
  have hW : 0 < W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hlogW : 0 ≤ log (W : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ W by omega))
  have hlogQ : 0 ≤ log (firstHitWheel W : ℝ) :=
    log_nonneg (by exact_mod_cast firstHitWheel_pos W)
  have hlogW2 : 0 ≤ log ((W : ℝ) + 2) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) W; linarith)
  let L₀ : ℝ := 1 + 7 * log ((W : ℝ) + 2) +
    2 * log (firstHitWheel W : ℝ) + log (W : ℝ) + 1000 * refinedHitTotalError
  have hL₀ : 0 < L₀ := by dsimp [L₀]; nlinarith [refinedHitTotalError_nonneg]
  refine ⟨L₀, hL₀, ?_⟩
  intro L hLL
  have hL : 0 < L := hL₀.trans_le hLL
  have hlarge : 7 * log ((W : ℝ) + 2) ≤ L := by dsimp [L₀] at hLL; nlinarith [refinedHitTotalError_nonneg]
  have hWheel : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L := by
    dsimp [L₀] at hLL
    nlinarith [refinedHitTotalError_nonneg]
  have herror : 1000 * refinedHitTotalError ≤ L := by dsimp [L₀] at hLL; nlinarith
  have hsmall : 7 * log (2 : ℝ) ≤ L := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (W : ℝ) + 2 by have := Nat.cast_nonneg (α := ℝ) W; linarith)
    linarith
  have hWR : W ≤ refinedHitPrimeCut L 24 := by
    have hwlog := log_le_log hW0 (show (W : ℝ) ≤ (W : ℝ) + 2 by linarith)
    have hh : (W : ℝ) ≤ exp (L / 7) := by
      calc
        (W : ℝ) = exp (log (W : ℝ)) := (exp_log hW0).symm
        _ ≤ exp (L / 7) := exp_le_exp.mpr (by linarith)
    convert Nat.le_floor hh using 1 <;> norm_num [refinedHitPrimeCut, refinedHitNode, firstHitNode]
  exact refinedHitMainSum_slack_of_finite_bound L hL herror
    (refinedHitMainSum_finite_bound L hL hsmall W hW hWR hWheel hthreshold hEuler)

#print axioms refinedHitMainSum_finite_bound
#print axioms exists_refinedHitMainSum_slack
end Erdos970.FiniteSelberg
