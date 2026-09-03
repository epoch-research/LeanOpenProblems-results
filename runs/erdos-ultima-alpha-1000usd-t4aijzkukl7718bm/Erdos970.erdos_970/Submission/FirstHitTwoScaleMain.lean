import Submission.FirstHitTwoScaleDefs

/-! The small-prime cutoff can be shortened while retaining a positive
first-hit main-term margin. This does not change the base power exponent. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma twoScaleMainSum_le (L : ℝ) :
    twoScaleMainSum L ≤ saturatedHitMainSum L +
      ∑ p ∈ (twoScaleSmallCut L+1).primesBelow, firstHitMeanExcess (L/2) p := by
  let S := (saturatedHitPrimeCut L 0+1).primesBelow
  have hh : twoScaleMainSum L ≤ saturatedHitMainSum L +
      ∑ p ∈ S.filter (fun p : ℕ => log (p : ℝ) ≤ L/100), firstHitMeanExcess (L/2) p := by
    unfold twoScaleMainSum saturatedHitMainSum
    rw [sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hpp := (WeightedMertens.mem_primes.mp hp).1
    have hn := firstHitMeanExcess_nonneg L p hpp
    dsimp only [twoScaleCutoff,twoScaleParameter]
    split_ifs with hsmall
    · unfold firstHitMeanExcess at *
      simp only [div_eq_mul_inv, one_mul] at hn ⊢
      nlinarith
    · simp
  apply hh.trans
  apply add_le_add le_rfl
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hsmall⟩ := mem_filter.mp hp
    have hpp := (WeightedMertens.mem_primes.mp hp).1
    exact WeightedMertens.mem_primes.mpr ⟨hpp,(log_le_twoScaleSmallCut L p hpp.pos).mp hsmall⟩
  · intro p hp _
    exact firstHitMeanExcess_nonneg _ _ (WeightedMertens.mem_primes.mp hp).1

/-- The shortened small-prime cutoff costs only a tiny fixed multiple of
1/L, together with an explicitly retained O(1/L^2) term. -/
lemma twoScale_small_excess_bound (L : ℝ) (hL : 0 < L) (W : ℕ) (hW : 0 < W)
    (hWheel : 2*log (firstHitWheel W : ℝ)+log (W : ℝ) ≤ L/2)
    (hthreshold : ∀ p, p.Prime → W < p → FirstHitLogThresholds p) :
    (∑ p ∈ (twoScaleSmallCut L+1).primesBelow, firstHitMeanExcess (L/2) p) ≤
      1/(10000*L)+WeightedMertens.sharpMomentError/L^2 := by
  let R := twoScaleSmallCut L
  let P := (R+1).primesBelow.filter (fun p => W < p)
  let C : ℝ := 6*9^8/(217*(L/2)^8)
  have hR : 0 < R := twoScaleSmallCut_pos L hL.le
  have hlogR : 0 ≤ log (R : ℝ) := log_natCast_nonneg R
  have hlog : log (R : ℝ) ≤ L/100 := twoScaleSmallCut_log_le L hL.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : (∑ p ∈ P, firstHitMeanExcess (L/2) p) ≤
      C * ∑ p ∈ (R+1).primesBelow, log (p : ℝ)^7/p := by
    calc
      _ ≤ ∑ p ∈ P, C * (log (p : ℝ)^7/p) := by
        apply sum_le_sum
        intro p hp
        have hpp := (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1
        have hpR := (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).2
        have hlp := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos)
          (show (p : ℝ) ≤ R by exact_mod_cast hpR)
        have ht := hthreshold p hpp (mem_filter.mp hp).2
        exact far_normalizer_excess_le p (firstHitCutoff (L/2) p) hpp
          (firstHitCutoff_pos _ _) (L/2) (by positivity) (by linarith)
          (firstHitCutoff_log_lower _ _) ht.1 ht.2.1
      _ = C * ∑ p ∈ P, log (p : ℝ)^7/p := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p _ _ => by positivity)) hC
  have hm := (abs_le.mp (WeightedMertens.prime_log_moment R hR 5)).2
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hm
  have h7 := pow_le_pow_left₀ hlogR hlog 7
  have h6 := pow_le_pow_left₀ hlogR hlog 6
  have hE := WeightedMertens.sharpMomentError_pos
  have h6' := mul_le_mul_of_nonneg_left h6 (show 0 ≤ 2*WeightedMertens.sharpMomentError by positivity)
  have hm' : (∑ p ∈ (R+1).primesBelow, log (p : ℝ)^7/p) ≤
      (L/100)^7/7+2*WeightedMertens.sharpMomentError*(L/100)^6 := by linarith
  have hupper := hs.trans (mul_le_mul_of_nonneg_left hm' hC)
  have heq : C*((L/100)^7/7+2*WeightedMertens.sharpMomentError*(L/100)^6) =
      (6*9^8*2^8/(1519*100^7 : ℝ))/L +
      (12*9^8*2^8/(217*100^6 : ℝ))*WeightedMertens.sharpMomentError/L^2 := by
    dsimp [C]
    field_simp
    ring
  rw [heq] at hupper
  have h1 : (6*9^8*2^8/(1519*100^7 : ℝ))/L ≤ 1/(10000*L) := by
    have hh := div_le_div_of_nonneg_right
      (by norm_num : (6*9^8*2^8/(1519*100^7 : ℝ)) ≤ 1/10000) hL.le
    simpa only [div_div] using hh
  have h2 : (12*9^8*2^8/(217*100^6 : ℝ))*WeightedMertens.sharpMomentError/L^2 ≤
      WeightedMertens.sharpMomentError/L^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg L)
    nlinarith only [mul_le_mul_of_nonneg_right
      (by norm_num : (12*9^8*2^8/(217*100^6 : ℝ)) ≤ 1) hE.le]
  have hpart := sum_filter_add_sum_filter_not (R+1).primesBelow (fun p => W < p) (firstHitMeanExcess (L/2))
  have hz : (∑ p ∈ (R+1).primesBelow with ¬ W < p, firstHitMeanExcess (L/2) p) = 0 := by
    apply sum_eq_zero
    intro p hp
    exact firstHitMeanExcess_zero_on_wheel W hW (L/2) hWheel p
      (WeightedMertens.mem_primes.mp (mem_filter.mp hp).1).1 (by have := (mem_filter.mp hp).2; omega)
  rw [hz,add_zero] at hpart
  change (∑ p ∈ P, firstHitMeanExcess (L/2) p) = _ at hpart
  rw [hpart] at hupper
  exact hupper.trans (add_le_add h1 h2)

/-- An unconditional main-term slack for the two-cutoff construction. -/
theorem exists_twoScaleMainSum_slack : ∃ L₀ : ℝ, 100 ≤ L₀ ∧
    ∀ L : ℝ, L₀ ≤ L → twoScaleMainSum L ≤ 1-1/(400*L) := by
  obtain ⟨M,hM,hmain⟩ := exists_saturatedHitMainSum_slack
  obtain ⟨W,hW2,hthreshold,_⟩ := exists_saturatedHit_threshold_wheel
  let L₀ := 100+M+4*log (firstHitWheel W : ℝ)+2*log (W : ℝ)+
    1000*WeightedMertens.sharpMomentError
  have hlogQ : 0 ≤ log (firstHitWheel W : ℝ) := log_nonneg (by exact_mod_cast firstHitWheel_pos W)
  have hlogW : 0 ≤ log (W : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ W by omega))
  have hE := WeightedMertens.sharpMomentError_pos
  have hL₀ : 100 ≤ L₀ := by dsimp [L₀]; linarith
  refine ⟨L₀,hL₀,?_⟩
  intro L hLL
  have hL : 0 < L := by linarith
  have hML : M ≤ L := by dsimp [L₀] at hLL; linarith
  have hWheel : 2*log (firstHitWheel W : ℝ)+log (W : ℝ) ≤ L/2 := by dsimp [L₀] at hLL; linarith
  have herr : 1000*WeightedMertens.sharpMomentError ≤ L := by dsimp [L₀] at hLL; linarith
  have he := twoScale_small_excess_bound L hL W (by omega) hWheel hthreshold
  have her : WeightedMertens.sharpMomentError/L^2 ≤ 1/(1000*L) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hL) (by positivity)).mpr
    nlinarith only [mul_nonneg hL.le (sub_nonneg.mpr herr)]
  have hr : 1/(10000*L)+1/(1000*L) ≤ 1/(400*L) := by
    field_simp
    nlinarith
  have hhalf : 1/(200*L) = 1/(400*L)+1/(400*L) := by ring
  have hb := twoScaleMainSum_le L
  have hc := hmain L hML
  rw [hhalf] at hc
  linarith

#print axioms exists_twoScaleMainSum_slack
end Erdos970.FiniteSelberg
