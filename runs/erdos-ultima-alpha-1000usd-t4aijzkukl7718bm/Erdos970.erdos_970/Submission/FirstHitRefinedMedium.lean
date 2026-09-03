import Submission.FirstHitRefinedGrid
import Submission.FirstHitMediumSum

/-! Assembly of the medium-prime first-hit excess over the rational grid.
The eventual Euler-product hypotheses are explicit in this finite theorem. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def refinedHitPrimeCut (L : ℝ) (j : ℕ) : ℕ :=
  ⌊exp (L / (2 * refinedHitNode j + 1))⌋₊
noncomputable def refinedHitPrimeBin (L : ℝ) (j : ℕ) : Finset ℕ :=
  (Ioc (refinedHitPrimeCut L (j + 1)) (refinedHitPrimeCut L j)).filter Nat.Prime
noncomputable def refinedHitMediumPrimes (L : ℝ) : Finset ℕ :=
  (Ioc (refinedHitPrimeCut L 24) (refinedHitPrimeCut L 0)).filter Nat.Prime
lemma refinedHitPrimeCut_antitone (L : ℝ) (hL : 0 ≤ L) : Antitone (refinedHitPrimeCut L) := by
  intro i j hij
  apply Nat.floor_le_floor
  apply exp_le_exp.mpr
  have hi0 : 0 < 2 * refinedHitNode i + 1 := by
    have := refinedHitNode_nonneg i
    linarith
  have hijr : refinedHitNode i ≤ refinedHitNode j := refinedHitNode_monotone hij
  exact div_le_div_of_nonneg_left hL hi0 (by linarith)

lemma refinedHit_bins_sum (L : ℝ) (hL : 0 ≤ L) (f : ℕ → ℝ) :
    (∑ j ∈ range 24, ∑ p ∈ refinedHitPrimeBin L j, f p) =
      ∑ p ∈ refinedHitMediumPrimes L, f p := by
  have ha := refinedHitPrimeCut_antitone L hL
  unfold refinedHitPrimeBin refinedHitMediumPrimes
  simp_rw [sum_prime_Ioc_eq_sub f _ _ (ha (Nat.le_succ _))]
  rw [sum_range_sub', sum_prime_Ioc_eq_sub f _ _ (ha (by omega : 0 ≤ 24))]

lemma refinedHitBin_subset_medium (L : ℝ) (hL : 0 ≤ L) (j : ℕ) (hj : j < 24) :
    refinedHitPrimeBin L j ⊆ refinedHitMediumPrimes L := by
  intro p hp
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo, hphi⟩ := mem_Ioc.mp hpI
  have ha := refinedHitPrimeCut_antitone L hL
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(ha (show j + 1 ≤ 24 by omega)).trans_lt hplo,
    hphi.trans (ha (Nat.zero_le j))⟩, hpp⟩

lemma refinedHitBin_log_bounds (L : ℝ) (j p : ℕ) (hp : p ∈ refinedHitPrimeBin L j) :
    p.Prime ∧ L / (2 * refinedHitNode (j + 1) + 1) < log (p : ℝ) ∧
      log (p : ℝ) ≤ L / (2 * refinedHitNode j + 1) := by
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo, hphi⟩ := mem_Ioc.mp hpI
  have hlo : exp (L / (2 * refinedHitNode (j + 1) + 1)) < (p : ℝ) := Nat.lt_of_floor_lt hplo
  have hhi : (p : ℝ) ≤ exp (L / (2 * refinedHitNode j + 1)) :=
    (show (p : ℝ) ≤ refinedHitPrimeCut L j by exact_mod_cast hphi).trans (Nat.floor_le (exp_pos _).le)
  have hhlo := log_lt_log (exp_pos _) hlo
  have hhhi := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos) hhi
  rw [log_exp] at hhlo hhhi
  exact ⟨hpp, hhlo, hhhi⟩

lemma refinedHitBin_ratio_mem (L : ℝ) (j p : ℕ) (hp : p ∈ refinedHitPrimeBin L j) :
    (L / log (p : ℝ) - 1) / 2 ∈ Set.Icc (refinedHitNode j) (refinedHitNode (j + 1)) := by
  obtain ⟨hpp, hlo, hhi⟩ := refinedHitBin_log_bounds L j p hp
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have hnode (i : ℕ) : 0 < 2 * refinedHitNode i + 1 := by
    have := refinedHitNode_nonneg i
    linarith
  have hlo' := (div_lt_iff₀ (hnode (j + 1))).mp hlo
  have hhi' := (le_div_iff₀ (hnode j)).mp hhi
  have hdiv : (L / log (p : ℝ)) * log (p : ℝ) = L := div_mul_cancel₀ _ hLp.ne'
  constructor <;> nlinarith only [hlo', hhi', hdiv, hLp]

lemma refinedHitMeanExcess_le_chord (L : ℝ) (j p : ℕ) (hj : j < 24)
    (hp : p ∈ refinedHitPrimeBin L j)
    (hthreshold : 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : eulerMass (p + 1).primesBelow ≤ (9 / 5 : ℝ) * log (p : ℝ)) :
    firstHitMeanExcess L p ≤
      (refinedHitExcessIntercept j + refinedHitExcessSlope j * ((L / log (p : ℝ) - 1) / 2)) /
        ((p : ℝ) * log p) := by
  let u := (L / log (p : ℝ) - 1) / 2
  have hpp := (refinedHitBin_log_bounds L j p hp).1
  have hu := refinedHitBin_ratio_mem L j p hp
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have harg : (L - log (p : ℝ)) / 2 = u * log p := by dsimp [u]; field_simp
  have hrec := (firstHitCutoff_reciprocal_upper_three_fifths L u p hpp hthreshold
    ((by norm_num : (3 / 5 : ℝ) ≤ 63 / 100).trans ((refinedHitNode_mem j (by omega)).1.trans hu.1))
    (hu.2.trans (refinedHitNode_mem (j + 1) (by omega)).2) harg).2
  have hchord := refinedHit_chord_upper j hj u hu
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hchord (by norm_num : (0 : ℝ) ≤ 10001 / 10000)) hLp.le
  have hEinv : 5 / (9 * log (p : ℝ)) ≤ 1 / eulerMass p.primesBelow := by
    have hh := one_div_le_one_div_of_le
      (eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2))
      ((eulerMass_strict_prefix_le p hpp).trans hEuler)
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub (hrec.trans hc) hEinv)
    (show 0 ≤ 1 / (p : ℝ) by positivity)
  unfold firstHitMeanExcess
  convert hh using 1
  unfold refinedHitExcessIntercept refinedHitExcessSlope
  dsimp [u]
  ring

/-- The actual medium-prime reciprocal excess, rather than just its model
profile, is bounded by the rational main term plus its explicit error. -/
theorem refinedHit_medium_sum_le (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L)
    (hthreshold : ∀ p ∈ refinedHitMediumPrimes L, 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : ∀ p ∈ refinedHitMediumPrimes L,
      eulerMass (p + 1).primesBelow ≤ (9 / 5 : ℝ) * log (p : ℝ)) :
    (∑ p ∈ refinedHitMediumPrimes L, firstHitMeanExcess L p) ≤
      (35213 / 36000) / L + refinedHitChordError / L ^ 2 := by
  rw [← refinedHit_bins_sum L hL.le]
  apply le_trans _ (refinedHit_affine_prime_sum_le L hL hsmall)
  apply sum_le_sum
  intro j hj
  change (∑ p ∈ refinedHitPrimeBin L j, firstHitMeanExcess L p) ≤
    ∑ p ∈ refinedHitPrimeBin L j, _
  apply sum_le_sum
  intro p hp
  have hm := refinedHitBin_subset_medium L hL.le j (mem_range.mp hj) hp
  exact refinedHitMeanExcess_le_chord L j p (mem_range.mp hj) hp (hthreshold p hm) (hEuler p hm)

#print axioms refinedHit_medium_sum_le
end Erdos970.FiniteSelberg
