import Submission.FirstHitMediumSum
import Submission.FirstHitEarlyTail

/-! Exact density telescoping, finite-wheel treatment, and assembly of the
first-hit main sum. A main-sum estimate alone is not a survivor certificate. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter

lemma inverse_eulerMass (P : Finset ℕ) :
    1 / eulerMass P = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  simp only [eulerMass, prod_inv_distrib, one_div, inv_inv]

lemma initial_density_telescope (R : ℕ) :
    (∑ p ∈ (R + 1).primesBelow, (1 / (p : ℝ)) * (1 / eulerMass p.primesBelow)) =
      1 - 1 / eulerMass (R + 1).primesBelow := by
  have hh := prod_one_sub_ordered (R + 1).primesBelow (fun p : ℕ => 1 / (p : ℝ))
  have hfilter (p : ℕ) (hp : p ∈ (R + 1).primesBelow) :
      (R + 1).primesBelow.filter (fun q => q < p) = p.primesBelow := by
    ext q
    have hpR := (WeightedMertens.mem_primes.mp hp).2
    simp only [mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hqr, hqprime⟩, hqp⟩
      exact ⟨hqp, hqprime⟩
    · rintro ⟨hqp, hqprime⟩
      exact ⟨⟨by omega, hqprime⟩, hqp⟩
  have hsum : (∑ p ∈ (R + 1).primesBelow,
      (1 / (p : ℝ)) * ∏ q ∈ (R + 1).primesBelow with q < p, (1 - 1 / (q : ℝ))) =
      ∑ p ∈ (R + 1).primesBelow, (1 / (p : ℝ)) * (1 / eulerMass p.primesBelow) := by
    apply sum_congr rfl
    intro p hp
    rw [hfilter p hp, inverse_eulerMass]
  rw [hsum, ← inverse_eulerMass] at hh
  linarith

lemma primeNormalizer_eq_eulerMass_of_prod_le (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hN : (∏ p ∈ P, p) ≤ N) : primeNormalizer P N = eulerMass P := by
  have hprod : 0 < ∏ p ∈ P, p := prod_pos (fun p hp => (hP p hp).pos)
  have hfull : smallDivisorFamily P N = P.powerset := by
    apply filter_eq_self.mpr
    intro Q hQ
    exact (Nat.le_of_dvd hprod (prod_dvd_prod_of_subset Q P id (mem_powerset.mp hQ))).trans hN
  change (∑ Q ∈ smallDivisorFamily P N, primeWeight Q) = _
  rw [hfull, primeWeight_sum_eq_eulerMass P hP]

noncomputable def firstHitWheel (W : ℕ) : ℕ := ∏ p ∈ (W + 1).primesBelow, p

lemma firstHitWheel_pos (W : ℕ) : 0 < firstHitWheel W :=
  prod_pos (fun p hp => (WeightedMertens.mem_primes.mp hp).1.pos)

lemma firstHitMeanExcess_zero_on_wheel (W : ℕ) (hW : 0 < W) (L : ℝ)
    (hL : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L)
    (p : ℕ) (hp : p.Prime) (hpW : p ≤ W) : firstHitMeanExcess L p = 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hQ0 : (0 : ℝ) < firstHitWheel W := by exact_mod_cast firstHitWheel_pos W
  have hlogp := log_le_log hp0 (show (p : ℝ) ≤ W by exact_mod_cast hpW)
  have hN : firstHitWheel W ≤ firstHitCutoff L p := by
    have hh : (firstHitWheel W : ℝ) ≤ exp ((L - log (p : ℝ)) / 2) := by
      rw [← exp_log hQ0]
      exact exp_le_exp.mpr (by linarith)
    exact_mod_cast hh.trans (Nat.le_ceil _)
  have hsub : p.primesBelow ⊆ (W + 1).primesBelow := by
    intro q hq
    obtain ⟨hqp, hqprime⟩ := Nat.mem_primesBelow.mp hq
    exact WeightedMertens.mem_primes.mpr ⟨hqprime, by omega⟩
  have hprod : (∏ q ∈ p.primesBelow, q) ≤ firstHitWheel W :=
    Nat.le_of_dvd (firstHitWheel_pos W) (prod_dvd_prod_of_subset _ _ id hsub)
  have he := primeNormalizer_eq_eulerMass_of_prod_le p.primesBelow (firstHitCutoff L p)
    (fun q hq => (Nat.mem_primesBelow.mp hq).2) (hprod.trans hN)
  simp only [firstHitMeanExcess, he, sub_self, mul_zero]

lemma firstHit_initial_split (L : ℝ) (hL : 0 ≤ L) (f : ℕ → ℝ) :
    (∑ p ∈ (firstHitPrimeCut L 0 + 1).primesBelow, f p) =
      (∑ p ∈ firstHitMediumPrimes L, f p) +
        ∑ p ∈ (firstHitPrimeCut L 23 + 1).primesBelow, f p := by
  have ha := firstHitPrimeCut_antitone L hL (by omega : 0 ≤ 23)
  have hsub : (firstHitPrimeCut L 23 + 1).primesBelow ⊆ (firstHitPrimeCut L 0 + 1).primesBelow := by
    intro p hp
    obtain ⟨hpp, hplo⟩ := WeightedMertens.mem_primes.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨hpp, hplo.trans ha⟩
  have he : ((firstHitPrimeCut L 0 + 1).primesBelow \ (firstHitPrimeCut L 23 + 1).primesBelow : Finset ℕ) =
      firstHitMediumPrimes L := by
    ext p
    simp only [firstHitMediumPrimes, Finset.mem_sdiff, mem_filter, mem_Ioc, WeightedMertens.mem_primes]
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

noncomputable def firstHitMainMargin : ℝ := 24 / 19 - (93 / 95 + 17 / 50000) - 42 / 155
noncomputable def firstHitTotalError : ℝ := firstHitChordError + 588 * WeightedMertens.sharpMomentError / 31

lemma firstHitMainMargin_gt : (11 / 1000 : ℝ) < firstHitMainMargin := by norm_num [firstHitMainMargin]

lemma firstHitTotalError_nonneg : 0 ≤ firstHitTotalError := by
  unfold firstHitTotalError firstHitChordError
  have hC := WeightedMertens.boundConstant_pos
  have hM := WeightedMertens.sharpMomentError_pos
  have hsum : 0 ≤ ∑ j ∈ range 23,
      (2 * |firstHitExcessIntercept j - firstHitExcessSlope j / 2| * (2 * firstHitNode (j + 1) + 1) ^ 2 +
        |firstHitExcessSlope j| * (2 * firstHitNode (j + 1) + 1) ^ 3) := by
    apply sum_nonneg
    intro j hj
    have hn : 0 ≤ 2 * firstHitNode (j + 1) + 1 := by
      have hh := (firstHitNode_mem (j + 1) (by have := mem_range.mp hj; omega)).1
      linarith
    positivity
  positivity


noncomputable def firstHitMainSum (L : ℝ) : ℝ :=
  ∑ p ∈ (firstHitPrimeCut L 0 + 1).primesBelow,
    (1 / (p : ℝ)) / primeNormalizer p.primesBelow (firstHitCutoff L p)

def FirstHitLogThresholds (p : ℕ) : Prop :=
  50 * WeightedMertens.sharpMomentError ≤ log (p : ℝ) ∧
  supportMassLogThreshold ≤ log (p : ℝ) ∧
  20000 * firstHitProfileError ≤ log (p : ℝ)

/-- All finite main-term estimates combined. The fixed small wheel, the
large-prime thresholds, and the Euler-product upper bound are explicit. -/
theorem firstHitMainSum_finite_bound (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L)
    (W : ℕ) (hW : 0 < W) (hWR : W ≤ firstHitPrimeCut L 23)
    (hWheel : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L)
    (hthreshold : ∀ p, p.Prime → W < p → FirstHitLogThresholds p)
    (hEuler : ∀ R : ℕ, W ≤ R → eulerMass (R + 1).primesBelow ≤ (19 / 10 : ℝ) * log (R : ℝ)) :
    firstHitMainSum L ≤ 1 - firstHitMainMargin / L + firstHitTotalError / L ^ 2 := by
  let R := firstHitPrimeCut L 23
  let Z := firstHitPrimeCut L 0
  have hR : 0 < R := lt_of_lt_of_le hW hWR
  have hRZ : R ≤ Z := firstHitPrimeCut_antitone L hL.le (by omega : 0 ≤ 23)
  have hZ : 0 < Z := hR.trans_le hRZ
  have hRL : 7 * log (R : ℝ) ≤ L := by
    have hh := log_le_log (show (0 : ℝ) < R by exact_mod_cast hR)
      (Nat.floor_le (exp_pos (L / (2 * firstHitNode 23 + 1))).le)
    rw [log_exp] at hh
    norm_num [firstHitNode] at hh
    linarith
  have hZL : log (Z : ℝ) ≤ 5 * L / 12 := by
    have hh := log_le_log (show (0 : ℝ) < Z by exact_mod_cast hZ)
      (Nat.floor_le (exp_pos (L / (2 * firstHitNode 0 + 1))).le)
    rw [log_exp] at hh
    norm_num [firstHitNode] at hh
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
  have hmidmem (p : ℕ) (hp : p ∈ firstHitMediumPrimes L) : p.Prime ∧ W < p := by
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    exact ⟨hpp, hWR.trans_lt (mem_Ioc.mp hpI).1⟩
  have hmedium := firstHit_medium_sum_le L hL hsmall
    (fun p hp => (hthreshold p (hmidmem p hp).1 (hmidmem p hp).2).2.2)
    (fun p hp => hEuler p (hmidmem p hp).2.le)
  have hextotal : (∑ p ∈ (Z + 1).primesBelow, firstHitMeanExcess L p) ≤
      (93 / 95 + 17 / 50000) / L + firstHitChordError / L ^ 2 +
        (42 / (155 * L) + 588 * WeightedMertens.sharpMomentError / (31 * L ^ 2)) := by
    rw [firstHit_initial_split L hL.le]
    exact add_le_add hmedium hearly
  have hE : eulerMass (Z + 1).primesBelow ≤ (19 / 24 : ℝ) * L := by
    have hh := hEuler Z (hWR.trans hRZ)
    linarith
  have hEinv : 24 / (19 * L) ≤ 1 / eulerMass (Z + 1).primesBelow := by
    have hh := one_div_le_one_div_of_le
      (eulerMass_pos (Z + 1).primesBelow (fun p hp => (WeightedMertens.mem_primes.mp hp).1)) hE
    convert hh using 1 <;> ring
  have hid : firstHitMainSum L = (∑ p ∈ (Z + 1).primesBelow, firstHitMeanExcess L p) +
      (1 - 1 / eulerMass (Z + 1).primesBelow) := by
    rw [← initial_density_telescope Z, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    unfold firstHitMeanExcess
    ring
  rw [hid]
  unfold firstHitMainMargin firstHitTotalError
  linear_combination hextotal + hEinv

lemma firstHitMainSum_slack_of_finite_bound (L : ℝ) (hL : 0 < L)
    (herror : 1000 * firstHitTotalError ≤ L)
    (hmain : firstHitMainSum L ≤ 1 - firstHitMainMargin / L + firstHitTotalError / L ^ 2) :
    firstHitMainSum L ≤ 1 - 1 / (100 * L) := by
  have herr : firstHitTotalError / L ^ 2 ≤ 1 / (1000 * L) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL) (by positivity)).mpr
    nlinarith only [mul_nonneg hL.le (show 0 ≤ L - 1000 * firstHitTotalError by linarith)]
  have hmargin := div_le_div_of_nonneg_right firstHitMainMargin_gt.le hL.le
  linear_combination hmain + herr + hmargin

lemma exists_firstHit_threshold_wheel : ∃ W : ℕ, 2 ≤ W ∧
    (∀ p, p.Prime → W < p → FirstHitLogThresholds p) ∧
    (∀ R : ℕ, W ≤ R → eulerMass (R + 1).primesBelow ≤ (19 / 10 : ℝ) * log (R : ℝ)) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_eulerMass_initial_le_nineteen_tenths_log
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
theorem exists_firstHitMainSum_slack : ∃ L₀ : ℝ, 0 < L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → firstHitMainSum L ≤ 1 - 1 / (100 * L) := by
  obtain ⟨W, hW2, hthreshold, hEuler⟩ := exists_firstHit_threshold_wheel
  have hW : 0 < W := by omega
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hlogW : 0 ≤ log (W : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ W by omega))
  have hlogQ : 0 ≤ log (firstHitWheel W : ℝ) :=
    log_nonneg (by exact_mod_cast firstHitWheel_pos W)
  have hlogW2 : 0 ≤ log ((W : ℝ) + 2) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) W; linarith)
  let L₀ : ℝ := 1 + 7 * log ((W : ℝ) + 2) +
    2 * log (firstHitWheel W : ℝ) + log (W : ℝ) + 1000 * firstHitTotalError
  have hL₀ : 0 < L₀ := by dsimp [L₀]; nlinarith [firstHitTotalError_nonneg]
  refine ⟨L₀, hL₀, ?_⟩
  intro L hLL
  have hL : 0 < L := hL₀.trans_le hLL
  have hlarge : 7 * log ((W : ℝ) + 2) ≤ L := by dsimp [L₀] at hLL; nlinarith [firstHitTotalError_nonneg]
  have hWheel : 2 * log (firstHitWheel W : ℝ) + log (W : ℝ) ≤ L := by
    dsimp [L₀] at hLL
    nlinarith [firstHitTotalError_nonneg]
  have herror : 1000 * firstHitTotalError ≤ L := by dsimp [L₀] at hLL; nlinarith
  have hsmall : 7 * log (2 : ℝ) ≤ L := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (W : ℝ) + 2 by have := Nat.cast_nonneg (α := ℝ) W; linarith)
    linarith
  have hWR : W ≤ firstHitPrimeCut L 23 := by
    have hwlog := log_le_log hW0 (show (W : ℝ) ≤ (W : ℝ) + 2 by linarith)
    have hh : (W : ℝ) ≤ exp (L / 7) := by
      calc
        (W : ℝ) = exp (log (W : ℝ)) := (exp_log hW0).symm
        _ ≤ exp (L / 7) := exp_le_exp.mpr (by linarith)
    convert Nat.le_floor hh using 1 <;> norm_num [firstHitPrimeCut, firstHitNode]
  exact firstHitMainSum_slack_of_finite_bound L hL herror
    (firstHitMainSum_finite_bound L hL hsmall W hW hWR hWheel hthreshold hEuler)

#print axioms firstHitMainSum_finite_bound
#print axioms exists_firstHitMainSum_slack
end Erdos970.FiniteSelberg
