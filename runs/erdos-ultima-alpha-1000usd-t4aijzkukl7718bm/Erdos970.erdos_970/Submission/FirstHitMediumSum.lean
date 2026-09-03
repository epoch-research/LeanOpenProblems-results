import Submission.FirstHitGrid

/-! Assembly of the medium-prime first-hit excess over the rational grid.
The eventual Euler-product hypotheses are explicit in this finite theorem. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def firstHitPrimeCut (L : ℝ) (j : ℕ) : ℕ :=
  ⌊exp (L / (2 * firstHitNode j + 1))⌋₊
noncomputable def firstHitPrimeBin (L : ℝ) (j : ℕ) : Finset ℕ :=
  (Ioc (firstHitPrimeCut L (j + 1)) (firstHitPrimeCut L j)).filter Nat.Prime
noncomputable def firstHitMediumPrimes (L : ℝ) : Finset ℕ :=
  (Ioc (firstHitPrimeCut L 23) (firstHitPrimeCut L 0)).filter Nat.Prime
noncomputable def firstHitMeanExcess (L : ℝ) (p : ℕ) : ℝ :=
  (1 / (p : ℝ)) * (1 / primeNormalizer p.primesBelow (firstHitCutoff L p) - 1 / eulerMass p.primesBelow)

lemma firstHitPrimeCut_antitone (L : ℝ) (hL : 0 ≤ L) : Antitone (firstHitPrimeCut L) := by
  intro i j hij
  apply Nat.floor_le_floor
  apply exp_le_exp.mpr
  have hi0 : 0 < 2 * firstHitNode i + 1 := by
    unfold firstHitNode
    have := Nat.cast_nonneg (α := ℝ) i
    linarith
  have hijr : firstHitNode i ≤ firstHitNode j := by
    unfold firstHitNode
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hij 7) (by norm_num)
  exact div_le_div_of_nonneg_left hL hi0 (by linarith)

lemma sum_prime_Ioc_eq_sub (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ p ∈ (Ioc a b).filter Nat.Prime, f p) =
      (∑ p ∈ range (b + 1), if p.Prime then f p else 0) -
        (∑ p ∈ range (a + 1), if p.Prime then f p else 0) := by
  have he : Ioc a b = Ico (a + 1) (b + 1) := by
    ext p
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [he, sum_filter, sum_Ico_eq_sub _ (by omega)]

lemma firstHit_bins_sum (L : ℝ) (hL : 0 ≤ L) (f : ℕ → ℝ) :
    (∑ j ∈ range 23, ∑ p ∈ firstHitPrimeBin L j, f p) =
      ∑ p ∈ firstHitMediumPrimes L, f p := by
  have ha := firstHitPrimeCut_antitone L hL
  unfold firstHitPrimeBin firstHitMediumPrimes
  simp_rw [sum_prime_Ioc_eq_sub f _ _ (ha (Nat.le_succ _))]
  rw [sum_range_sub', sum_prime_Ioc_eq_sub f _ _ (ha (by omega : 0 ≤ 23))]

lemma firstHitBin_subset_medium (L : ℝ) (hL : 0 ≤ L) (j : ℕ) (hj : j < 23) :
    firstHitPrimeBin L j ⊆ firstHitMediumPrimes L := by
  intro p hp
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo, hphi⟩ := mem_Ioc.mp hpI
  have ha := firstHitPrimeCut_antitone L hL
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(ha (show j + 1 ≤ 23 by omega)).trans_lt hplo,
    hphi.trans (ha (Nat.zero_le j))⟩, hpp⟩

lemma firstHitBin_log_bounds (L : ℝ) (j p : ℕ) (hp : p ∈ firstHitPrimeBin L j) :
    p.Prime ∧ L / (2 * firstHitNode (j + 1) + 1) < log (p : ℝ) ∧
      log (p : ℝ) ≤ L / (2 * firstHitNode j + 1) := by
  obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
  obtain ⟨hplo, hphi⟩ := mem_Ioc.mp hpI
  have hlo : exp (L / (2 * firstHitNode (j + 1) + 1)) < (p : ℝ) := Nat.lt_of_floor_lt hplo
  have hhi : (p : ℝ) ≤ exp (L / (2 * firstHitNode j + 1)) :=
    (show (p : ℝ) ≤ firstHitPrimeCut L j by exact_mod_cast hphi).trans (Nat.floor_le (exp_pos _).le)
  have hhlo := log_lt_log (exp_pos _) hlo
  have hhhi := log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos) hhi
  rw [log_exp] at hhlo hhhi
  exact ⟨hpp, hhlo, hhhi⟩

lemma firstHitBin_ratio_mem (L : ℝ) (j p : ℕ) (hp : p ∈ firstHitPrimeBin L j) :
    (L / log (p : ℝ) - 1) / 2 ∈ Set.Icc (firstHitNode j) (firstHitNode (j + 1)) := by
  obtain ⟨hpp, hlo, hhi⟩ := firstHitBin_log_bounds L j p hp
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have hnode (i : ℕ) : 0 < 2 * firstHitNode i + 1 := by
    unfold firstHitNode
    have := Nat.cast_nonneg (α := ℝ) i
    linarith
  have hlo' := (div_lt_iff₀ (hnode (j + 1))).mp hlo
  have hhi' := (le_div_iff₀ (hnode j)).mp hhi
  have hdiv : (L / log (p : ℝ)) * log (p : ℝ) = L := div_mul_cancel₀ _ hLp.ne'
  constructor <;> nlinarith only [hlo', hhi', hdiv, hLp]

lemma eulerMass_strict_prefix_le (p : ℕ) (hp : p.Prime) :
    eulerMass p.primesBelow ≤ eulerMass (p + 1).primesBelow := by
  rw [eulerMass_strict_prefix hp]
  have he := eulerMass_pos (p + 1).primesBelow (fun q hq => (WeightedMertens.mem_primes.mp hq).1)
  have hh : 0 ≤ 1 / (p : ℝ) := by positivity
  nlinarith only [mul_nonneg he.le hh]

lemma firstHitMeanExcess_le_chord (L : ℝ) (j p : ℕ) (hj : j < 23)
    (hp : p ∈ firstHitPrimeBin L j)
    (hthreshold : 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : eulerMass (p + 1).primesBelow ≤ (19 / 10 : ℝ) * log (p : ℝ)) :
    firstHitMeanExcess L p ≤
      (firstHitExcessIntercept j + firstHitExcessSlope j * ((L / log (p : ℝ) - 1) / 2)) /
        ((p : ℝ) * log p) := by
  let u := (L / log (p : ℝ) - 1) / 2
  have hpp := (firstHitBin_log_bounds L j p hp).1
  have hu := firstHitBin_ratio_mem L j p hp
  have hLp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have harg : (L - log (p : ℝ)) / 2 = u * log p := by dsimp [u]; field_simp
  have hrec := (firstHitCutoff_reciprocal_upper L u p hpp hthreshold
    ((firstHitNode_mem j (by omega)).1.trans hu.1)
    (hu.2.trans (firstHitNode_mem (j + 1) (by omega)).2) harg).2
  have hchord := firstHit_chord_upper j hj u hu
  have hc := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hchord (by norm_num : (0 : ℝ) ≤ 10001 / 10000)) hLp.le
  have hEinv : 10 / (19 * log (p : ℝ)) ≤ 1 / eulerMass p.primesBelow := by
    have hh := one_div_le_one_div_of_le
      (eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2))
      ((eulerMass_strict_prefix_le p hpp).trans hEuler)
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub (hrec.trans hc) hEinv)
    (show 0 ≤ 1 / (p : ℝ) by positivity)
  unfold firstHitMeanExcess
  convert hh using 1
  unfold firstHitExcessIntercept firstHitExcessSlope
  dsimp [u]
  ring

/-- The actual medium-prime reciprocal excess, rather than just its model
profile, is bounded by the rational main term plus its explicit error. -/
theorem firstHit_medium_sum_le (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L)
    (hthreshold : ∀ p ∈ firstHitMediumPrimes L, 20000 * firstHitProfileError ≤ log (p : ℝ))
    (hEuler : ∀ p ∈ firstHitMediumPrimes L,
      eulerMass (p + 1).primesBelow ≤ (19 / 10 : ℝ) * log (p : ℝ)) :
    (∑ p ∈ firstHitMediumPrimes L, firstHitMeanExcess L p) ≤
      (93 / 95 + 17 / 50000) / L + firstHitChordError / L ^ 2 := by
  rw [← firstHit_bins_sum L hL.le]
  apply le_trans _ (firstHit_affine_prime_sum_le L hL hsmall)
  apply sum_le_sum
  intro j hj
  change (∑ p ∈ firstHitPrimeBin L j, firstHitMeanExcess L p) ≤
    ∑ p ∈ firstHitPrimeBin L j, _
  apply sum_le_sum
  intro p hp
  have hm := firstHitBin_subset_medium L hL.le j (mem_range.mp hj) hp
  exact firstHitMeanExcess_le_chord L j p (mem_range.mp hj) hp (hthreshold p hm) (hEuler p hm)

#print axioms firstHit_medium_sum_le
end Erdos970.FiniteSelberg
