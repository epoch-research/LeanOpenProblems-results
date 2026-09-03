import Submission.ComplementPrefixArithmetic

/-! Uniform witness error for all complementary-index prefixes X≤B^k. -/
namespace Erdos371
open Finset FiniteSieve

lemma untruncatedComplementPrefix_witness_point_error (B C k X n : ℕ) (hB : 1 < B)
    (hX : X ≤ B^k) (hC : B^k ≤ C) (P : Finset ℕ) (hP : largePrimeSet B C ⊆ P) :
    |untruncatedComplementPrefix B X n-nonzeroFullParity n*
      localPatternWitness (primesThrough B) P (shortComplementPattern (largePrimeSet B C) X k) n| ≤
      (if n=0 then (1 : ℝ) else 0)+
        (if (activeBlockPrimes (largePrimeSet B C)
          (activePrimeAtoms (largePrimeSet B C) n)).card ≤ k then (2 : ℝ)^(k+1) else 0) := by
  by_cases hn : n=0
  · subst n
    rw [untruncatedComplementPrefix_zero]
    simp only [nonzeroFullParity,if_true,zero_mul,sub_zero]
    have hb : |if 1 ≤ X then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    exact hb.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
  · have hn0 : 0 < n := by omega
    rw [if_neg hn]
    simp only [nonzeroFullParity,if_neg hn,zero_add,localPatternWitness]
    rw [← shortComplementPattern_congr (largePrimeSet B C) X k _ _
      (activePrimeAtoms_locality _ P hP n)]
    by_cases hc : (activeBlockPrimes (largePrimeSet B C)
        (activePrimeAtoms (largePrimeSet B C) n)).card ≤ k
    · rw [if_pos hc]
      have hp : subsetPolynomial k (activeBlockPrimes (largePrimeSet B C)
          (activePrimeAtoms (largePrimeSet B C) n)).card ≤ (2 : ℝ)^k :=
        (subsetPolynomial_le_two_pow _ _).trans (pow_le_pow_right₀ (by norm_num) hc)
      have ha := (untruncatedComplementPrefix_abs_le B C k X n hB hn0 hX hC).trans hp
      have hb := (shortComplementPattern_abs_le (largePrimeSet B C) X k
        (activePrimeAtoms (largePrimeSet B C) n)).trans hp
      have hprod : |fullRadicalParity n*(naturalBlockParity (primesThrough B) n*
          shortComplementPattern (largePrimeSet B C) X k
            (activePrimeAtoms (largePrimeSet B C) n))| ≤ (2 : ℝ)^k := by
        rw [abs_mul,abs_mul,fullRadicalParity_abs,one_mul]
        have he : |naturalBlockParity (primesThrough B) n|=1 := blockParity_abs _ _
        rwa [he,one_mul]
      exact (abs_sub _ _).trans (by rw [pow_succ]; linarith)
    · rw [if_neg hc,untruncatedComplementPrefix_eq_pattern B C k X n hB hn0 hX hC (by omega),
        mul_assoc,sub_self,abs_zero]

/-- No unbounded endpoint error is discarded: n=0 contributes at most 1/N,
and low-occupancy inputs contribute at most 2^(k+1) times their proportion. -/
theorem untruncatedComplementPrefix_witness_mean_error (B C k X N : ℕ) (hB : 1 < B)
    (hX : X ≤ B^k) (hC : B^k ≤ C) (P : Finset ℕ) (hP : largePrimeSet B C ⊆ P) :
    |(∑ n ∈ range N, untruncatedComplementPrefix B X n)/N-
      (∑ n ∈ range N, nonzeroFullParity n*
        localPatternWitness (primesThrough B) P
          (shortComplementPattern (largePrimeSet B C) X k) n)/N| ≤
      1/(N : ℝ)+(2 : ℝ)^(k+1)*(thinPrimeBlockCount (largePrimeSet B C) k N : ℝ)/N := by
  have h0 : (∑ n ∈ range N, if n=0 then (1 : ℝ) else 0) ≤ 1 := by
    simp only [sum_ite_eq',mem_range]
    split_ifs <;> norm_num
  have he : (∑ n ∈ range N, if (activeBlockPrimes (largePrimeSet B C)
      (activePrimeAtoms (largePrimeSet B C) n)).card ≤ k then (2 : ℝ)^(k+1) else 0) =
      (2 : ℝ)^(k+1)*(thinPrimeBlockCount (largePrimeSet B C) k N : ℝ) := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    dsimp only [thinPrimeBlockCount]
    ring
  have hs := sum_le_sum (s := range N) (fun n _ => untruncatedComplementPrefix_witness_point_error B C k X n hB hX hC P hP)
  rw [sum_add_distrib,he] at hs
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  calc
    _ ≤ (∑ n ∈ range N, |untruncatedComplementPrefix B X n-nonzeroFullParity n*
        localPatternWitness (primesThrough B) P
          (shortComplementPattern (largePrimeSet B C) X k) n|)/N :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
    _ ≤ (1+(2 : ℝ)^(k+1)*(thinPrimeBlockCount (largePrimeSet B C) k N : ℝ))/N :=
      div_le_div_of_nonneg_right (hs.trans (add_le_add h0 le_rfl)) (Nat.cast_nonneg N)
    _ = _ := by ring

#print axioms untruncatedComplementPrefix_witness_mean_error
end Erdos371
