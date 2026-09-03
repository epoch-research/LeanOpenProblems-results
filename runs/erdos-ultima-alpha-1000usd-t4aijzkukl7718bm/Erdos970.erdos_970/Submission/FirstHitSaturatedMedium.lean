import Submission.FirstHitSaturatedGrid
import Submission.FirstHitMediumSum

/-! Assembly of the medium-prime first-hit excess over the rational grid.
The eventual Euler-product hypotheses are explicit in this finite theorem. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def saturatedHitPrimeCut (L : ℝ) (j : ℕ) : ℕ :=
  ⌊exp (L / (2 * saturatedHitNode j + 1))⌋₊
noncomputable def saturatedHitPrimeBin (L : ℝ) (j : ℕ) : Finset ℕ :=
  (Ioc (saturatedHitPrimeCut L (j + 1)) (saturatedHitPrimeCut L j)).filter Nat.Prime
noncomputable def saturatedHitMediumPrimes (L : ℝ) : Finset ℕ :=
  (Ioc (saturatedHitPrimeCut L 24) (saturatedHitPrimeCut L 0)).filter Nat.Prime
lemma saturatedHitPrimeCut_antitone (L : ℝ) (hL : 0 ≤ L) : Antitone (saturatedHitPrimeCut L) := by
  intro i j hij
  apply Nat.floor_le_floor
  apply exp_le_exp.mpr
  have hi0 : 0 < 2 * saturatedHitNode i + 1 := by
    have := saturatedHitNode_nonneg i
    linarith
  have hijr : saturatedHitNode i ≤ saturatedHitNode j := saturatedHitNode_monotone hij
  exact div_le_div_of_nonneg_left hL hi0 (by linarith)

lemma saturatedHit_bins_sum (L : ℝ) (hL : 0 ≤ L) (f : ℕ → ℝ) :
    (∑ j ∈ range 24, ∑ p ∈ saturatedHitPrimeBin L j, f p) =
      ∑ p ∈ saturatedHitMediumPrimes L, f p := by
  have ha := saturatedHitPrimeCut_antitone L hL
  unfold saturatedHitPrimeBin saturatedHitMediumPrimes
  simp_rw [sum_prime_Ioc_eq_sub f _ _ (ha (Nat.le_succ _))]
  rw [sum_range_sub', sum_prime_Ioc_eq_sub f _ _ (ha (by omega : 0 ≤ 24))]

lemma saturatedHitBin_subset_medium (L : ℝ) (hL : 0 ≤ L) (j : ℕ) (hj : j < 24) :
    saturatedHitPrimeBin L j ⊆ saturatedHitMediumPrimes L := by
  intro p hp
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo, hphi⟩ := mem_Ioc.mp hpI
  have ha := saturatedHitPrimeCut_antitone L hL
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(ha (show j + 1 ≤ 24 by omega)).trans_lt hplo,
    hphi.trans (ha (Nat.zero_le j))⟩, hpp⟩

lemma saturatedHitBin_log_bounds (L : ℝ) (j p : ℕ) (hp : p ∈ saturatedHitPrimeBin L j) :
    p.Prime ∧ L / (2 * saturatedHitNode (j + 1) + 1) < log (p : ℝ) ∧
      log (p : ℝ) ≤ L / (2 * saturatedHitNode j + 1) := by
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo, hphi⟩ := mem_Ioc.mp hpI
  have hlo : exp (L / (2 * saturatedHitNode (j + 1) + 1)) < (p : ℝ) := Nat.lt_of_floor_lt hplo
  have hhi : (p : ℝ) ≤ exp (L / (2 * saturatedHitNode j + 1)) :=
    (show (p : ℝ) ≤ saturatedHitPrimeCut L j by exact_mod_cast hphi).trans (Nat.floor_le (exp_pos _).le)
  have hhlo := log_lt_log (exp_pos _) hlo
  have hhhi := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos) hhi
  rw [log_exp] at hhlo hhhi
  exact ⟨hpp, hhlo, hhhi⟩

lemma saturatedHitBin_ratio_mem (L : ℝ) (j p : ℕ) (hp : p ∈ saturatedHitPrimeBin L j) :
    (L / log (p : ℝ) - 1) / 2 ∈ Set.Icc (saturatedHitNode j) (saturatedHitNode (j + 1)) := by
  obtain ⟨hpp, hlo, hhi⟩ := saturatedHitBin_log_bounds L j p hp
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have hnode (i : ℕ) : 0 < 2 * saturatedHitNode i + 1 := by
    have := saturatedHitNode_nonneg i
    linarith
  have hlo' := (div_lt_iff₀ (hnode (j + 1))).mp hlo
  have hhi' := (le_div_iff₀ (hnode j)).mp hhi
  have hdiv : (L / log (p : ℝ)) * log (p : ℝ) = L := div_mul_cancel₀ _ hLp.ne'
  constructor <;> nlinarith only [hlo', hhi', hdiv, hLp]

lemma saturatedHitMeanExcess_le_chord (L : ℝ) (j p : ℕ) (hj : j < 24)
    (hp : p ∈ saturatedHitPrimeBin L j)
    (hthreshold : 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : eulerMass (p + 1).primesBelow ≤ (9 / 5 : ℝ) * log (p : ℝ)) :
    firstHitMeanExcess L p ≤
      (saturatedHitExcessIntercept j + saturatedHitExcessSlope j * ((L / log (p : ℝ) - 1) / 2)) /
        ((p : ℝ) * log p) := by
  let u := (L / log (p : ℝ) - 1) / 2
  have hpp := (saturatedHitBin_log_bounds L j p hp).1
  have hu := saturatedHitBin_ratio_mem L j p hp
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have harg : (L - log (p : ℝ)) / 2 = u * log p := by dsimp [u]; field_simp
  have hrec := (firstHitCutoff_reciprocal_upper_eleven_twentieths L u p hpp hthreshold
    ((by norm_num : (11 / 20 : ℝ) ≤ 29 / 50).trans ((saturatedHitNode_mem j (by omega)).1.trans hu.1))
    (hu.2.trans (saturatedHitNode_mem (j + 1) (by omega)).2) harg).2
  have hchord := saturatedHit_chord_upper j hj u hu
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
  unfold saturatedHitExcessIntercept saturatedHitExcessSlope
  dsimp [u]
  ring

/-- The actual medium-prime reciprocal excess, rather than just its model
profile, is bounded by the rational main term plus its explicit error. -/
theorem saturatedHit_medium_sum_le (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L)
    (hthreshold : ∀ p ∈ saturatedHitMediumPrimes L, 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : ∀ p ∈ saturatedHitMediumPrimes L,
      eulerMass (p + 1).primesBelow ≤ (9 / 5 : ℝ) * log (p : ℝ)) :
    (∑ p ∈ saturatedHitMediumPrimes L, firstHitMeanExcess L p) ≤
      (109 / 100) / L + saturatedHitChordError / L ^ 2 := by
  rw [← saturatedHit_bins_sum L hL.le]
  apply le_trans _ (saturatedHit_affine_prime_sum_le L hL hsmall)
  apply sum_le_sum
  intro j hj
  change (∑ p ∈ saturatedHitPrimeBin L j, firstHitMeanExcess L p) ≤
    ∑ p ∈ saturatedHitPrimeBin L j, _
  apply sum_le_sum
  intro p hp
  have hm := saturatedHitBin_subset_medium L hL.le j (mem_range.mp hj) hp
  exact saturatedHitMeanExcess_le_chord L j p (mem_range.mp hj) hp (hthreshold p hm) (hEuler p hm)

#print axioms saturatedHit_medium_sum_le
end Erdos970.FiniteSelberg
