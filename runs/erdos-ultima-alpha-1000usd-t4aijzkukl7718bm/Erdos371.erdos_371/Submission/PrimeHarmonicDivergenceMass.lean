import Submission.PrimeWinnerHarmonicFlux

/-! The difference of limiting winner and loser harmonic currents has an
explicit summable divergence. Its positive part away from label one has
mass one and a uniformly bounded prime-label tail. This does not control
the signed circulation shared by the two current vectors. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def reciprocalFluxStep (n : ℕ) : ℝ :=
  1/(n+1 : ℝ)-1/(n+2 : ℝ)

lemma reciprocalFluxStep_nonneg (n : ℕ) : 0≤reciprocalFluxStep n := by
  unfold reciprocalFluxStep
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))

lemma reciprocalFluxStep_sum (N : ℕ) :
    (∑ n ∈ range N, reciprocalFluxStep n)=1-1/(N+1 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih,reciprocalFluxStep]
    push_cast
    ring

lemma reciprocalFluxStep_hasSum : HasSum reciprocalFluxStep 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg reciprocalFluxStep_nonneg]
  simp_rw [reciprocalFluxStep_sum]
  simpa only [sub_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1

noncomputable def primeDivergenceTerm (p n : ℕ) : ℝ :=
  primeLabelIndicator p (n+2)*reciprocalFluxStep n

lemma primeDivergenceTerm_nonneg (p n : ℕ) : 0≤primeDivergenceTerm p n :=
  mul_nonneg (primeLabelIndicator_nonneg p (n+2)) (reciprocalFluxStep_nonneg n)

lemma primeDivergenceTerm_le_step (p n : ℕ) :
    primeDivergenceTerm p n≤reciprocalFluxStep n := by
  unfold primeDivergenceTerm primeLabelIndicator
  split_ifs <;> simp [reciprocalFluxStep_nonneg]

lemma primeDivergenceTerm_summable (p : ℕ) : Summable (primeDivergenceTerm p) :=
  Summable.of_nonneg_of_le (primeDivergenceTerm_nonneg p)
    (primeDivergenceTerm_le_step p) reciprocalFluxStep_hasSum.summable

noncomputable def primeDivergenceMass (p : ℕ) : ℝ := ∑' n, primeDivergenceTerm p n

lemma primeDivergenceMass_nonneg (p : ℕ) : 0≤primeDivergenceMass p :=
  tsum_nonneg (primeDivergenceTerm_nonneg p)

lemma primeDivergenceMass_eq_zero_of_le_one (p : ℕ) (hp : p≤1) : primeDivergenceMass p=0 := by
  have hterm (n : ℕ) : primeDivergenceTerm p n=0 := by
    have hlarge : 1<Nat.maxPrimeFac (n+2) := (Nat.one_lt_maxPrimeFac_iff (n+2)).mpr (by omega)
    simp [primeDivergenceTerm,primeLabelIndicator,show Nat.maxPrimeFac (n+2)≠p by omega]
  simp only [primeDivergenceMass,hterm,tsum_zero]

lemma primeLabel_boundary_tendsto_zero (p : ℕ) :
    Tendsto (fun N : ℕ => primeLabelIndicator p (N+2)/(N+1 : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero _ _ tendsto_one_div_add_atTop_nhds_zero_nat
  · intro N
    exact div_nonneg (primeLabelIndicator_nonneg p (N+2)) (by positivity)
  · intro N
    unfold primeLabelIndicator
    split_ifs
    · exact le_rfl
    · rw [zero_div]; positivity

/-- Exact infinite flux, including the exceptional negative source at
label one. The remaining term is a positive reciprocal derivative mass. -/
theorem primeHarmonicLimit_flux_exact (p : ℕ) :
    primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p =
      primeDivergenceMass p-primeLabelIndicator p 1 := by
  have hl := ((rawPrimeWinnerHarmonic_tendsto p).sub (rawPrimeLoserHarmonic_tendsto p)).comp
    (tendsto_add_atTop_nat 2)
  have hr := ((primeLabel_boundary_tendsto_zero p).sub_const (primeLabelIndicator p 1)).add
    (primeDivergenceTerm_summable p).hasSum.tendsto_sum_nat
  have he := hr.congr (fun N => (rawPrimeHarmonic_flux p N).symm)
  have h := tendsto_nhds_unique hl he
  change primeWinnerHarmonicLimit p-primeLoserHarmonicLimit p =
    0-primeLabelIndicator p 1+primeDivergenceMass p at h
  linarith

lemma primeDivergenceMass_prefix (B : ℕ) :
    (∑ p ∈ range B, primeDivergenceMass p) =
      ∑' n, if Nat.maxPrimeFac (n+2)<B then reciprocalFluxStep n else 0 := by
  unfold primeDivergenceMass
  rw [← Summable.tsum_finsetSum (fun p (_ : p∈range B) => primeDivergenceTerm_summable p)]
  apply tsum_congr
  intro n
  simp [primeDivergenceTerm,primeLabelIndicator,ite_mul]

/-- The positive divergence masses form a probability distribution on
prime labels at least two. -/
theorem primeDivergenceMass_hasSum : HasSum primeDivergenceMass 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg primeDivergenceMass_nonneg 1).mpr
  simp_rw [primeDivergenceMass_prefix]
  have ht (n : ℕ) : Tendsto (fun B : ℕ =>
      if Nat.maxPrimeFac (n+2)<B then reciprocalFluxStep n else 0) atTop (𝓝 (reciprocalFluxStep n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (Nat.maxPrimeFac (n+2))] with B hB
    simp only [if_pos hB]
  have hb : ∀ B n : ℕ, ‖(if Nat.maxPrimeFac (n+2)<B then reciprocalFluxStep n else 0)‖ ≤
      reciprocalFluxStep n := by
    intro B n
    split_ifs <;> simp [Real.norm_eq_abs,abs_of_nonneg (reciprocalFluxStep_nonneg n),
      reciprocalFluxStep_nonneg n]
  have h := tendsto_tsum_of_dominated_convergence reciprocalFluxStep_hasSum.summable ht
    (Eventually.of_forall hb)
  simpa only [reciprocalFluxStep_hasSum.tsum_eq] using h

lemma primeDivergenceMass_prefix_lower (B : ℕ) (hB : 2≤B) :
    1-1/(B-1 : ℝ) ≤ ∑ p ∈ range B, primeDivergenceMass p := by
  rw [primeDivergenceMass_prefix]
  let f : ℕ → ℝ := fun n => if Nat.maxPrimeFac (n+2)<B then reciprocalFluxStep n else 0
  have hf0 (n : ℕ) : 0≤f n := by dsimp [f]; split_ifs <;> simp [reciprocalFluxStep_nonneg]
  have hf : Summable f := Summable.of_nonneg_of_le hf0
    (fun n => by dsimp [f]; split_ifs <;> simp [reciprocalFluxStep_nonneg]) reciprocalFluxStep_hasSum.summable
  have hs := hf.sum_le_tsum (range (B-2)) (fun n _ => hf0 n)
  have he : (∑ n ∈ range (B-2), f n) = 1-1/(B-1 : ℝ) := by
    calc
      _ = ∑ n ∈ range (B-2), reciprocalFluxStep n := by
        apply sum_congr rfl
        intro n hn
        have hlt : Nat.maxPrimeFac (n+2)<B := by
          have hp := Nat.maxPrimeFac_le (n := n+2)
          have hn' := mem_range.mp hn
          omega
        simp only [f,if_pos hlt]
      _ = 1-1/((B-2 : ℕ)+1 : ℝ) := reciprocalFluxStep_sum (B-2)
      _ = _ := by rw [Nat.cast_sub hB]; push_cast; ring
  rw [he] at hs
  exact hs

/-- Explicit l1 control of the divergence beyond every prime cutoff. -/
theorem primeDivergenceMass_tail_bound (B : ℕ) (hB : 2≤B) :
    (∑' j, primeDivergenceMass (j+B)) ≤ 1/(B-1 : ℝ) := by
  have he := primeDivergenceMass_hasSum.summable.sum_add_tsum_nat_add B
  rw [primeDivergenceMass_hasSum.tsum_eq] at he
  linarith [primeDivergenceMass_prefix_lower B hB]

/-- Winning and losing limiting-current tails differ by an explicitly
summable vector. This is not a bound for either current tail separately. -/
theorem primeHarmonicLimit_flux_l1_tail_bound (B : ℕ) (hB : 2≤B) :
    (∑' j, ‖primeWinnerHarmonicLimit (j+B)-primeLoserHarmonicLimit (j+B)‖) ≤
      1/(B-1 : ℝ) := by
  have he (j : ℕ) : ‖primeWinnerHarmonicLimit (j+B)-primeLoserHarmonicLimit (j+B)‖ =
      primeDivergenceMass (j+B) := by
    rw [primeHarmonicLimit_flux_exact]
    have hz : primeLabelIndicator (j+B) 1=0 := by
      simp [primeLabelIndicator,show 1≠j+B by omega]
    rw [hz,sub_zero,Real.norm_eq_abs,abs_of_nonneg (primeDivergenceMass_nonneg _)]
  simp_rw [he]
  exact primeDivergenceMass_tail_bound B hB

#print axioms primeHarmonicLimit_flux_exact
#print axioms primeDivergenceMass_hasSum
#print axioms primeHarmonicLimit_flux_l1_tail_bound
end Erdos371
