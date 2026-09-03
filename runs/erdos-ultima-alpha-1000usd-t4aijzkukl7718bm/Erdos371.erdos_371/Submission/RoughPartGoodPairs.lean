import Submission.LargePrimeSquares
import Submission.ReciprocalDiscrepancy

/-! Almost all consecutive pairs have squarefree, large rough parts inside
the prescribed rectangle. These pairs will witness non-negligible absolute
mass of the reciprocal-discrepancy kernel. -/

namespace Erdos371

lemma smallRoughPartCount_ratio_bound (B N : ℕ) (hN : 1 < N) :
    (smallRoughPartCount B N : ℝ) / N ≤
      4 / Real.log N + 16 * (Real.log (B + 1 : ℝ) / Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h := smallRoughPartCount_log_bound B N hN
  have he : 4 / Real.log N + 16 * (Real.log (B + 1 : ℝ) / Real.log N) =
      (4 * N + 16 * N * Real.log (B + 1 : ℝ)) / (N * Real.log N) := by field_simp
  rw [he, le_div_iff₀ (mul_pos hN0 hlog)]
  convert h using 1 <;> field_simp

open Filter in
lemma subpower_log_ratio_succ (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log (N + 1 : ℝ)) atTop (nhds 0) := by
  apply squeeze_zero_norm' _ hB
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hn : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hnum : 0 ≤ Real.log (B N + 1 : ℝ) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (B N)
    linarith)
  have hden : Real.log N ≤ Real.log (N + 1 : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum (hn.le.trans hden))]
  exact div_le_div_of_nonneg_left hnum hn hden

open Filter in
theorem smallRoughPartCount_succ_tendsto_zero (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => (smallRoughPartCount (B N) (N + 1) : ℝ) / N) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1 : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have ht := ((tendsto_inv_atTop_zero.comp hlog).const_mul (4 : ℝ)).add
    ((subpower_log_ratio_succ B hB).const_mul (16 : ℝ))
  simp only [mul_zero, add_zero] at ht
  have hs : Tendsto (fun N => (smallRoughPartCount (B N) (N + 1) : ℝ) / (N + 1 : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
      smallRoughPartCount_ratio_bound (B N) (N + 1) (by omega)
  have hr : Tendsto (fun N : ℕ => (N + 1 : ℝ) / N) atTop (nhds 1) := by
    have ht := tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    field_simp
  have hp := hs.mul hr
  simp only [zero_mul] at hp
  apply hp.congr
  intro N
  field_simp

/-- An integer is bad if its rough part is too small, contains a repeated
large prime, or has no intervening prime to force a sufficiently large cofactor. -/
def badRoughPart (B K M m : ℕ) : Prop :=
  (roughPrimePart B m)^4 ≤ M^3 ∨
    (∃ p, p.Prime ∧ B < p ∧ p^2 ∣ m) ∨
      (∀ p ∈ mediumPrimes K B, ¬p ∣ m)

noncomputable instance (B K M m : ℕ) : Decidable (badRoughPart B K M m) := Classical.propDecidable _

noncomputable def badRoughPartCount (B K M : ℕ) : ℕ :=
  ((Finset.range M).filter fun n => badRoughPart B K M (n + 1)).card

noncomputable def goodRoughPairSet (B K N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n =>
    ¬badRoughPart B K (N + 1) (n + 1) ∧ ¬badRoughPart B K (N + 1) (n + 2)

lemma badRoughPartCount_bound (B K M : ℕ) :
    badRoughPartCount B K M ≤ smallRoughPartCount B M + largePrimeSquareCount B M +
      primeAvoidCount (mediumPrimes K B) M := by
  classical
  have ht (n : ℕ) : (if badRoughPart B K M (n + 1) then 1 else 0) ≤
      (if (roughPrimePart B (n + 1))^4 ≤ M^3 then 1 else 0) +
      (if ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n + 1 then 1 else 0) +
      (if ∀ p ∈ mediumPrimes K B, ¬p ∣ n + 1 then 1 else 0 : ℕ) := by
    by_cases h1 : (roughPrimePart B (n + 1))^4 ≤ M^3 <;>
      by_cases h2 : ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n + 1 <;>
      by_cases h3 : ∀ p ∈ mediumPrimes K B, ¬p ∣ n + 1 <;>
      simp [badRoughPart, h1, h2, h3] <;> omega
  have h := Finset.sum_le_sum (s := Finset.range M) (fun n _ => ht n)
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, badRoughPartCount,
    smallRoughPartCount, largePrimeSquareCount, primeAvoidCount] using h

lemma shifted_predicate_card_le (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.range N).filter fun n => P (n + 2)).card ≤
      ((Finset.range (N + 1)).filter fun n => P (n + 1)).card := by
  apply Finset.card_le_card_of_injOn (fun n => n + 1)
  · intro n hn
    simp only [Finset.mem_coe] at hn ⊢
    obtain ⟨hnN, hP⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hnN; omega), ?_⟩
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hP
  · intro n hn m hm he
    dsimp only at he
    omega

lemma goodRoughPairSet_card_lower (B K N : ℕ) :
    N ≤ (goodRoughPairSet B K N).card + 2 * badRoughPartCount B K (N + 1) := by
  let P := badRoughPart B K (N + 1)
  have ht (n : ℕ) : (1 : ℕ) ≤
      (if ¬P (n + 1) ∧ ¬P (n + 2) then 1 else 0) +
      (if P (n + 1) then 1 else 0) + (if P (n + 2) then 1 else 0) := by
    by_cases h1 : P (n + 1) <;> by_cases h2 : P (n + 2) <;> simp [h1, h2]
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => ht n)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    Finset.sum_add_distrib, Finset.sum_boole] at h
  have h1 : ((Finset.range N).filter fun n => P (n + 1)).card ≤ badRoughPartCount B K (N + 1) :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
  have h2 := shifted_predicate_card_le P N
  change _ ≤ badRoughPartCount B K (N + 1) at h2
  change _ ≤ (goodRoughPairSet B K N).card + _ + _ at h
  norm_cast at h
  omega

open Filter in
theorem badRoughPartCount_quantile_tendsto_zero (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => (badRoughPartCount (B N) (harmonicCofactorCutoff (B N)) (N + 1) : ℝ) / N)
      atTop (nhds 0) := by
  have ht := ((smallRoughPartCount_succ_tendsto_zero B hB).add
    (largePrimeSquareCount_succ_tendsto_zero B hBatTop)).add
      (harmonicCofactorCutoff_avoid_count_succ_tendsto B hBatTop (subpower_cutoff_eventually_le B hB))
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  rw [← add_div, ← add_div]
  have hc := badRoughPartCount_bound (B N) (harmonicCofactorCutoff (B N)) (N + 1)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg N)

open Filter in
theorem goodRoughPairSet_quantile_density_one (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => ((goodRoughPairSet (B N) (harmonicCofactorCutoff (B N)) N).card : ℝ) / N)
      atTop (nhds 1) := by
  have ht := (badRoughPartCount_quantile_tendsto_zero B hBatTop hB).const_mul (2 : ℝ)
  simp only [mul_zero] at ht
  have hd : Tendsto (fun N => 1 -
      ((goodRoughPairSet (B N) (harmonicCofactorCutoff (B N)) N).card : ℝ) / N)
      atTop (nhds 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hupper : ((goodRoughPairSet (B N) (harmonicCofactorCutoff (B N)) N).card : ℝ) ≤ N := by
      exact_mod_cast (Finset.card_filter_le (Finset.range N) _).trans_eq (Finset.card_range N)
    have hnonneg : 0 ≤ 1 - ((goodRoughPairSet (B N) (harmonicCofactorCutoff (B N)) N).card : ℝ) / N := by
      apply sub_nonneg.mpr
      exact (div_le_one hN0).mpr hupper
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have hl : (N : ℝ) ≤ ((goodRoughPairSet (B N) (harmonicCofactorCutoff (B N)) N).card : ℝ) +
        2 * badRoughPartCount (B N) (harmonicCofactorCutoff (B N)) (N + 1) := by
      exact_mod_cast goodRoughPairSet_card_lower (B N) (harmonicCofactorCutoff (B N)) N
    apply (le_of_mul_le_mul_right ?_ hN0)
    field_simp
    linarith
  have h := hd.const_sub 1
  simp only [sub_zero] at h
  apply h.congr
  intro N
  ring

lemma good_rough_part_data (B K N m : ℕ) (hN : 2 ≤ N) (hm : 0 < m) (hmN : m ≤ N + 1)
    (hgood : ¬badRoughPart B K (N + 1) m) :
    1 < roughPrimePart B m ∧ Squarefree (roughPrimePart B m) ∧
      B < (roughPrimePart B m).minFac ∧ K * roughPrimePart B m ≤ N ∧
      2 * N + 1 < (roughPrimePart B m)^2 := by
  simp only [badRoughPart, not_or] at hgood
  have hpow : (N + 1)^3 < (roughPrimePart B m)^4 := Nat.lt_of_not_ge hgood.1
  have hN2 : N + 1 ≤ N^2 := by nlinarith
  have hcube : (2 * N + 1)^2 ≤ (N + 1)^3 := by
    nlinarith [Nat.mul_le_mul_left N hN2]
  have ha2 : 2 * N + 1 < (roughPrimePart B m)^2 := by
    by_contra h
    have hle : (roughPrimePart B m)^2 ≤ 2 * N + 1 := by omega
    have hsq := Nat.pow_le_pow_left hle 2
    nlinarith
  have ha1 : 1 < roughPrimePart B m := by nlinarith
  have hmin := roughPrimePart_minFac B m ha1
  have hdiv := roughPrimePart_dvd B m hm.ne'
  refine ⟨ha1, roughPrimePart_squarefree B m hm.ne' ?_, hmin, ?_, ha2⟩
  · intro p hp hpB hpsq
    exact hgood.2.1 ⟨p, hp, hpB, hpsq⟩
  · by_contra h
    have hNa : N < K * roughPrimePart B m := by omega
    have hma : m ≤ K * roughPrimePart B m := by omega
    have hprod := Nat.mul_div_cancel' hdiv
    have hq : m / roughPrimePart B m ≤ K := by nlinarith
    exact hgood.2.2 (rough_divisor_avoids_medium B K m (roughPrimePart B m)
      (Nat.mem_divisors.mpr ⟨hdiv, hm.ne'⟩) hmin hq)

#print axioms smallRoughPartCount_succ_tendsto_zero
#print axioms goodRoughPairSet_quantile_density_one
#print axioms good_rough_part_data
end Erdos371
