import Submission.ShortComplementArithmetic
import Submission.ThinPrimeBlocks
import Submission.LocalPatternSelection

/-! Mean error between the actual short divisor sum and its local witness.
The exceptional input zero is suppressed only in the bounded target. -/
namespace Erdos371
open Finset FiniteSieve

lemma subsetPolynomial_le_two_pow (k m : ℕ) : subsetPolynomial k m ≤ (2 : ℝ)^m := by
  rw [← card_range m,subsetPolynomial_eq_powerset]
  calc
    _ ≤ ∑ _E ∈ (range m).powerset, (1 : ℝ) := by
      apply sum_le_sum
      intro E _
      split_ifs <;> norm_num
    _ = _ := by simp

lemma divisorSideColour_abs (n d : ℕ) : |divisorSideColour n d|=1 := by
  unfold divisorSideColour
  split_ifs <;> norm_num

lemma roughRadical_moebius_abs (B m : ℕ) :
    |(ArithmeticFunction.moebius (roughRadical B m) : ℝ)|=1 := by
  rw [roughRadical_moebius_parity]
  simp only [abs_pow,abs_neg,abs_one,one_pow]

lemma shortRoughComplement_zero (B k : ℕ) (hB : 0 < B) : shortRoughComplement B k 0=1 := by
  have hp : 1 ≤ B^k := Nat.pow_pos hB
  simp [shortRoughComplement,roughRadical,divisorSideColour,hp]

lemma shortRoughComplement_abs_le (B C k n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hC : B^k ≤ C) :
    |shortRoughComplement B k n| ≤
      subsetPolynomial k (activeBlockPrimes (largePrimeSet B C)
        (activePrimeAtoms (largePrimeSet B C) n)).card := by
  rw [shortRoughComplement_eq_block_sum B C k n hB hn hC,abs_mul,
    roughRadical_moebius_abs,one_mul,subsetPolynomial_eq_powerset]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro E _
  by_cases hc : E.card ≤ k
  · rw [if_pos hc]
    split_ifs
    · rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,divisorSideColour_abs]
    · norm_num
  · rw [if_neg hc,if_neg (not_and_of_not_left _ hc),abs_zero]

noncomputable def nonzeroFullParity (n : ℕ) : ℝ := if n=0 then 0 else fullRadicalParity n

lemma nonzeroFullParity_abs_le (n : ℕ) : |nonzeroFullParity n| ≤ 1 := by
  unfold nonzeroFullParity
  split_ifs
  · norm_num
  · exact (fullRadicalParity_abs n).le

lemma shortRoughComplement_witness_point_error (B C k n : ℕ) (hB : 1 < B)
    (hC : B^k ≤ C) (P : Finset ℕ) (hP : largePrimeSet B C ⊆ P) :
    |shortRoughComplement B k n-nonzeroFullParity n*
      localPatternWitness (primesThrough B) P (shortComplementPattern (largePrimeSet B C) (B^k) k) n| ≤
      (if n=0 then (1 : ℝ) else 0)+
        (if (activeBlockPrimes (largePrimeSet B C)
          (activePrimeAtoms (largePrimeSet B C) n)).card ≤ k then (2 : ℝ)^(k+1) else 0) := by
  by_cases hn : n=0
  · subst n
    rw [shortRoughComplement_zero B k (by omega)]
    simp only [nonzeroFullParity,if_true,zero_mul,sub_zero,abs_one]
    exact le_add_of_nonneg_right (by split_ifs <;> positivity)
  · have hn0 : 0 < n := by omega
    rw [if_neg hn]
    simp only [nonzeroFullParity,if_neg hn,zero_add,localPatternWitness]
    rw [← shortComplementPattern_congr (largePrimeSet B C) (B^k) k _ _
      (activePrimeAtoms_locality _ P hP n)]
    by_cases hc : (activeBlockPrimes (largePrimeSet B C)
        (activePrimeAtoms (largePrimeSet B C) n)).card ≤ k
    · rw [if_pos hc]
      have hp : subsetPolynomial k (activeBlockPrimes (largePrimeSet B C)
          (activePrimeAtoms (largePrimeSet B C) n)).card ≤ (2 : ℝ)^k :=
        (subsetPolynomial_le_two_pow _ _).trans (pow_le_pow_right₀ (by norm_num) hc)
      have ha := (shortRoughComplement_abs_le B C k n hB hn0 hC).trans hp
      have hb := (shortComplementPattern_abs_le (largePrimeSet B C) (B^k) k
        (activePrimeAtoms (largePrimeSet B C) n)).trans hp
      have hprod : |fullRadicalParity n*(naturalBlockParity (primesThrough B) n*
          shortComplementPattern (largePrimeSet B C) (B^k) k
            (activePrimeAtoms (largePrimeSet B C) n))| ≤ (2 : ℝ)^k := by
        rw [abs_mul,abs_mul,fullRadicalParity_abs,one_mul]
        have he : |naturalBlockParity (primesThrough B) n|=1 := blockParity_abs _ _
        rwa [he,one_mul]
      exact (abs_sub _ _).trans (by rw [pow_succ]; linarith)
    · rw [if_neg hc,shortRoughComplement_eq_pattern B C k n hB hn0 hC (by omega),
        mul_assoc,sub_self,abs_zero]

/-- No unbounded endpoint error is discarded: n=0 contributes at most 1/N,
and low-occupancy inputs contribute at most 2^(k+1) times their proportion. -/
theorem shortRoughComplement_witness_mean_error (B C k N : ℕ) (hB : 1 < B)
    (hC : B^k ≤ C) (P : Finset ℕ) (hP : largePrimeSet B C ⊆ P) :
    |(∑ n ∈ range N, shortRoughComplement B k n)/N-
      (∑ n ∈ range N, nonzeroFullParity n*
        localPatternWitness (primesThrough B) P
          (shortComplementPattern (largePrimeSet B C) (B^k) k) n)/N| ≤
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
  have hs := sum_le_sum (s := range N) (fun n _ => shortRoughComplement_witness_point_error B C k n hB hC P hP)
  rw [sum_add_distrib,he] at hs
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  calc
    _ ≤ (∑ n ∈ range N, |shortRoughComplement B k n-nonzeroFullParity n*
        localPatternWitness (primesThrough B) P
          (shortComplementPattern (largePrimeSet B C) (B^k) k) n|)/N :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
    _ ≤ (1+(2 : ℝ)^(k+1)*(thinPrimeBlockCount (largePrimeSet B C) k N : ℝ))/N :=
      div_le_div_of_nonneg_right (hs.trans (add_le_add h0 le_rfl)) (Nat.cast_nonneg N)
    _ = _ := by ring

#print axioms shortRoughComplement_witness_mean_error
end Erdos371
