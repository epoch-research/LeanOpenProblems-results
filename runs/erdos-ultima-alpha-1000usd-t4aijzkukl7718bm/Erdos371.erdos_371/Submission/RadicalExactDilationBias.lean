import Submission.ExactDilationBias
import Submission.LargePrimeSquares

/-! Removing repeated large prime factors makes the biased auxiliary family
also invariant under every positive power. The large-prime square tail bounds
the mean cost. No maximum-under-multiplication identity is assumed. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter MultiplicativeChirpObstruction
open scoped Topology

noncomputable def strippedChirpHom (t : ℝ) (B : ℕ) : ℕ →*₀ ℂ where
  toFun := strippedChirp t B
  map_zero' := strippedChirp_zero t B
  map_one' := by simp [strippedChirp]
  map_mul' := strippedChirp_mul t B

lemma strippedChirp_prime (t : ℝ) (B p : ℕ) (hp : p.Prime) :
    strippedChirp t B p = if p ≤ B then 1 else chirp t p := by
  by_cases h : p ≤ B
  · rw [if_pos h]
    exact strippedChirp_small t B p hp.pos h
  · rw [if_neg h,strippedChirp]
    have he : (∏ q ∈ (B+1).primesBelow, (starRingEnd ℂ) (chirp t q)^p.factorization q) = 1 := by
      apply prod_eq_one
      intro q hq
      have hqB := (Nat.mem_primesBelow.mp hq).1
      have hqp : p ≠ q := by omega
      simp [hp.factorization,hqp]
    rw [he,mul_one]

lemma strippedChirp_prime_product (t : ℝ) (B n : ℕ) (hn : n ≠ 0) :
    strippedChirp t B n = ∏ p ∈ n.primeFactors, (if p ≤ B then 1 else chirp t p)^n.factorization p := by
  have he := congrArg (strippedChirpHom t B) (Nat.factorization_prod_pow_eq_self hn)
  simp only [Finsupp.prod,Nat.support_factorization,map_prod,map_pow] at he
  change (∏ p ∈ n.primeFactors, strippedChirp t B p ^ n.factorization p) = strippedChirp t B n at he
  rw [← he]
  apply prod_congr rfl
  intro p hp
  rw [strippedChirp_prime t B p (Nat.mem_primeFactors.mp hp).1]

noncomputable def radicalChirp (t : ℝ) (B n : ℕ) : ℂ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, if p ≤ B then 1 else chirp t p

lemma radicalChirp_norm_le_one (t : ℝ) (B n : ℕ) : ‖radicalChirp t B n‖ ≤ 1 := by
  unfold radicalChirp
  split_ifs with hn
  · norm_num
  · rw [norm_prod]
    apply prod_le_one
    · intro p _; exact norm_nonneg _
    · intro p _
      split_ifs
      · simp
      · exact chirp_norm_le_one t p

lemma radicalChirp_small_multiplier (t : ℝ) (B k n : ℕ) (hk : 0 < k) (hkB : k ≤ B) :
    radicalChirp t B (k*n) = radicalChirp t B n := by
  classical
  by_cases hn : n = 0
  · subst n; simp
  unfold radicalChirp
  rw [if_neg (mul_ne_zero hk.ne' hn),if_neg hn,Nat.primeFactors_mul hk.ne' hn]
  symm
  apply prod_subset subset_union_right
  intro p hp hpn
  have hpk : p ∈ k.primeFactors := (mem_union.mp hp).resolve_right hpn
  have hple : p ≤ B := (Nat.le_of_dvd hk (Nat.mem_primeFactors.mp hpk).2.1).trans hkB
  rw [if_pos hple]

lemma radicalChirp_pow (t : ℝ) (B n r : ℕ) (hr : 0 < r) :
    radicalChirp t B (n^r) = radicalChirp t B n := by
  by_cases hn : n = 0
  · simp [hn,zero_pow hr.ne']
  simp only [radicalChirp,if_neg hn,if_neg (pow_ne_zero _ hn),Nat.primeFactors_pow n hr.ne']

lemma radicalChirp_eq_stripped_of_no_square (t : ℝ) (B n : ℕ)
    (h : ¬∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n) :
    radicalChirp t B n = strippedChirp t B n := by
  by_cases hn : n = 0
  · simp [hn,radicalChirp,strippedChirp_zero]
  rw [radicalChirp,if_neg hn,strippedChirp_prime_product t B n hn]
  apply prod_congr rfl
  intro p hp
  by_cases hpB : p ≤ B
  · simp [hpB]
  · have hpp := (Nat.mem_primeFactors.mp hp).1
    have hpos : 0 < n.factorization p := by
      apply Nat.pos_of_ne_zero
      exact Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
    have hlt : n.factorization p < 2 := by
      by_contra he
      exact h ⟨p,hpp,by omega,(hpp.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩
    have he : n.factorization p = 1 := by omega
    simp [hpB,he]

lemma radicalChirp_error_sum (t : ℝ) (B N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖radicalChirp t B n-strippedChirp t B n‖) ≤ 2*largePrimeSquareCount B N := by
  classical
  have hp (n : ℕ) : ‖radicalChirp t B n-strippedChirp t B n‖ ≤
      2*(if ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n then (1 : ℝ) else 0) := by
    split_ifs with h
    · have ht := norm_sub_le (radicalChirp t B n) (strippedChirp t B n)
      linarith [radicalChirp_norm_le_one t B n,strippedChirp_norm_le_one t B n]
    · rw [radicalChirp_eq_stripped_of_no_square t B n h]
      norm_num
  have he : (∑ n ∈ Icc 1 N, if ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n then (1 : ℝ) else 0) =
      largePrimeSquareCount B N := by
    have hs := sum_Ico_add' (fun n => if ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n then (1 : ℝ) else 0) 0 N 1
    simp only [zero_add,Nat.Ico_zero_eq_range,Ico_add_one_right_eq_Icc] at hs
    rw [← hs]
    simp [largePrimeSquareCount]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, 2*(if ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n then (1 : ℝ) else 0) :=
      sum_le_sum fun n _ => hp n
    _ = _ := by rw [← mul_sum,he]

noncomputable def squareTail (B : ℕ) : ℝ :=
  (∑' p : ℕ, (1 : ℝ)/(p : ℝ)^2)-∑ p ∈ range (B+1), (1 : ℝ)/(p : ℝ)^2

lemma squareTail_nonneg (B : ℕ) : 0 ≤ squareTail B := by
  apply sub_nonneg.mpr
  exact Summable.sum_le_tsum _ (by intros; positivity)
    (Real.summable_one_div_nat_pow.mpr (by norm_num))

lemma squareTail_tendsto : Tendsto squareTail atTop (nhds 0) := by
  have hs : Summable (fun p : ℕ => (1 : ℝ)/(p : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_sub
    (∑' p : ℕ, (1 : ℝ)/(p : ℝ)^2)
  simpa only [sub_self] using ht

lemma radicalChirp_bias_error (t : ℝ) (B N : ℕ) (hN : 0 < N) :
    |imaginaryBias (radicalChirp t B) N-imaginaryBias (strippedChirp t B) N| ≤ 8*squareTail B := by
  have he := imaginaryBias_error (radicalChirp t B) (strippedChirp t B)
    (radicalChirp_norm_le_one t B) (strippedChirp_norm_le_one t B) N
  have hs := radicalChirp_error_sum t B (N+1)
  have hcount := largePrimeSquareCount_ratio_bound B (N+1) (by omega)
  change (largePrimeSquareCount B (N+1) : ℝ)/(N+1 : ℕ) ≤ squareTail B at hcount
  have hcount' := (div_le_iff₀ (by positivity : (0 : ℝ) < (N+1 : ℕ))).mp hcount
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply he.trans
  apply (div_le_iff₀ hNr).mpr
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at hcount'
  nlinarith [squareTail_nonneg B]

/-- The exact-invariance obstruction can also satisfy positive-power
invariance. Thus that extra identity alone does not fill the natural gap. -/
theorem exists_exact_dilation_and_power_stable_biased_family :
    ∃ N : ℕ → ℕ, ∃ F : ℕ → ℕ → ℂ,
      Tendsto N atTop atTop ∧
      (∀ j n, ‖F j n‖ ≤ 1) ∧
      (∀ j k, 0 < k → k ≤ j → ∀ n, F j (k*n) = F j n) ∧
      (∀ j n r, 0 < r → F j (n^r) = F j n) ∧
      ∀ j, (1/240 : ℝ) ≤ imaginaryBias (F j) (N j) := by
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp (squareTail_tendsto.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1/10000))
  have hex (j : ℕ) := exists_stripped_biased_chirp (max B₀ j)
  choose N hNB hN9 hb using hex
  refine ⟨N,fun j => radicalChirp (N j) (max B₀ j),
    tendsto_atTop_mono (fun j => (le_max_right _ _).trans (hNB j)) tendsto_id,?_,?_,?_,?_⟩
  · intro j n
    exact radicalChirp_norm_le_one _ _ _
  · intro j k hk hkj n
    exact radicalChirp_small_multiplier _ _ _ _ hk (hkj.trans (le_max_right _ _))
  · intro j n r hr
    exact radicalChirp_pow _ _ _ _ hr
  · intro j
    have he := radicalChirp_bias_error (N j) (max B₀ j) (N j) (by have := hN9 j; omega)
    have ht := hB₀ (max B₀ j) (le_max_left _ _)
    have hlo := (abs_le.mp he).1
    change (1/240 : ℝ) ≤ imaginaryBias (radicalChirp (N j) (max B₀ j)) (N j)
    linarith [hb j]

#print axioms radicalChirp_small_multiplier
#print axioms radicalChirp_pow
#print axioms exists_exact_dilation_and_power_stable_biased_family
end Erdos371.ExactMultiplierChirpObstruction
