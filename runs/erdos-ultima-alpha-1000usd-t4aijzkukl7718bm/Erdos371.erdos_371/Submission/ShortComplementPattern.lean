import Submission.PolynomialPatternTail
import Submission.PrimeBlockWitness

/-! Local coloured patterns for short complementary divisors. The summation
retains both the deletion parity and the product bound. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

noncomputable def shortComplementPattern (B : Finset ℕ) (X k : ℕ)
    (U : Finset PrimeAtom) : ℝ :=
  ∑ E ∈ (activeBlockPrimes B U).powerset,
    if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ X then
      (-1 : ℝ)^E.card*firstBlockColour (B\E) U else 0

lemma shortComplementPattern_odd (B : Finset ℕ) (X k : ℕ) (U : Finset PrimeAtom) :
    shortComplementPattern B X k (U.map (primeColourFlip B).toEmbedding) =
      -shortComplementPattern B X k U := by
  unfold shortComplementPattern
  rw [activeBlockPrimes_flip,← sum_neg_distrib]
  apply sum_congr rfl
  intro E _
  rw [firstBlockColour_flip (B\E) B U sdiff_subset]
  split_ifs <;> ring

lemma shortComplementPattern_flip_disjoint (B C : Finset ℕ) (hBC : Disjoint B C)
    (X k : ℕ) (U : Finset PrimeAtom) :
    shortComplementPattern B X k (U.map (primeColourFlip C).toEmbedding) =
      shortComplementPattern B X k U := by
  unfold shortComplementPattern
  rw [activeBlockPrimes_flip]
  apply sum_congr rfl
  intro E _
  rw [firstBlockColour_flip_disjoint (B\E) C U (hBC.mono_left sdiff_subset)]

lemma shortComplementPattern_congr (B : Finset ℕ) (X k : ℕ) (U V : Finset PrimeAtom)
    (h : ∀ p ∈ B, ∀ b : Bool, (p,b) ∈ U ↔ (p,b) ∈ V) :
    shortComplementPattern B X k U = shortComplementPattern B X k V := by
  unfold shortComplementPattern
  rw [activeBlockPrimes_congr B U V h]
  apply sum_congr rfl
  intro E _
  rw [firstBlockColour_congr (B\E) U V (fun p hp => h p (Finset.mem_sdiff.mp hp).1)]

lemma shortComplementPattern_abs_le (B : Finset ℕ) (X k : ℕ) (U : Finset PrimeAtom) :
    |shortComplementPattern B X k U| ≤ subsetPolynomial k (activeBlockPrimes B U).card := by
  rw [subsetPolynomial_eq_powerset]
  unfold shortComplementPattern
  calc
    _ ≤ ∑ E ∈ (activeBlockPrimes B U).powerset,
        |if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ X then
          (-1 : ℝ)^E.card*firstBlockColour (B\E) U else 0| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro E _
      by_cases hc : E.card ≤ k
      · rw [if_pos hc]
        split_ifs
        · rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
          exact firstBlockColour_abs_le _ _
        · norm_num
      · rw [if_neg hc,if_neg (not_and_of_not_left _ hc),abs_zero]

lemma activeBlockPrimes_card_le (B : Finset ℕ) (U : Finset PrimeAtom) :
    (activeBlockPrimes B U).card ≤ U.card := by
  have hsub : activeBlockPrimes B U ⊆ U.image Prod.fst := by
    intro p hp
    rcases (mem_filter.mp hp).2 with h | h
    · exact mem_image.mpr ⟨(p,false),h,rfl⟩
    · exact mem_image.mpr ⟨(p,true),h,rfl⟩
  exact (card_le_card hsub).trans card_image_le

noncomputable def clippedShortComplementPattern (B : Finset ℕ) (X k R : ℕ)
    (U : Finset PrimeAtom) : ℝ :=
  if (activeBlockPrimes B U).card < R then shortComplementPattern B X k U else 0

lemma clippedShortComplementPattern_abs_le (B : Finset ℕ) (X k R : ℕ)
    (U : Finset PrimeAtom) :
    |clippedShortComplementPattern B X k R U| ≤ subsetPolynomial k R := by
  unfold clippedShortComplementPattern
  split_ifs with h
  · exact (shortComplementPattern_abs_le B X k U).trans (subsetPolynomial_mono k h.le)
  · simpa using subsetPolynomial_nonneg k R

lemma clippedShortComplementPattern_odd (B : Finset ℕ) (X k R : ℕ) (U : Finset PrimeAtom) :
    clippedShortComplementPattern B X k R (U.map (primeColourFlip B).toEmbedding) =
      -clippedShortComplementPattern B X k R U := by
  unfold clippedShortComplementPattern
  rw [activeBlockPrimes_flip,shortComplementPattern_odd]
  split_ifs <;> ring

lemma clippedShortComplementPattern_flip_disjoint (B C : Finset ℕ) (hBC : Disjoint B C)
    (X k R : ℕ) (U : Finset PrimeAtom) :
    clippedShortComplementPattern B X k R (U.map (primeColourFlip C).toEmbedding) =
      clippedShortComplementPattern B X k R U := by
  unfold clippedShortComplementPattern
  rw [activeBlockPrimes_flip,shortComplementPattern_flip_disjoint B C hBC]

lemma clippedShortComplementPattern_congr (B : Finset ℕ) (X k R : ℕ) (U V : Finset PrimeAtom)
    (h : ∀ p ∈ B, ∀ b : Bool, (p,b) ∈ U ↔ (p,b) ∈ V) :
    clippedShortComplementPattern B X k R U = clippedShortComplementPattern B X k R V := by
  unfold clippedShortComplementPattern
  rw [activeBlockPrimes_congr B U V h,shortComplementPattern_congr B X k U V h]

lemma clippedShortComplementPattern_error (B : Finset ℕ) (X k R : ℕ)
    (U : Finset PrimeAtom) :
    |shortComplementPattern B X k U-clippedShortComplementPattern B X k R U| ≤
      if R ≤ (activeBlockPrimes B U).card then
        subsetPolynomial k (activeBlockPrimes B U).card else 0 := by
  unfold clippedShortComplementPattern
  by_cases h : (activeBlockPrimes B U).card < R
  · rw [if_pos h,if_neg (by omega),sub_self,abs_zero]
  · rw [if_neg h,if_pos (by omega),sub_zero]
    exact shortComplementPattern_abs_le B X k U

/-- The clipping error can be estimated using the already controlled atom
factorial moments. The ambient prime set P does not enter the moment bound. -/
lemma clippedShortComplementPattern_arithmetic_error (B P : Finset ℕ) (hBP : B ⊆ P)
    (X k R n : ℕ) :
    |shortComplementPattern B X k (activePrimeAtoms P n)-
      clippedShortComplementPattern B X k R (activePrimeAtoms P n)| ≤
      if R ≤ (activePrimeAtoms B n).card then
        subsetPolynomial k (activePrimeAtoms B n).card else 0 := by
  rw [← shortComplementPattern_congr B X k _ _ (activePrimeAtoms_locality B P hBP n),
    ← clippedShortComplementPattern_congr B X k R _ _ (activePrimeAtoms_locality B P hBP n)]
  refine (clippedShortComplementPattern_error B X k R _).trans ?_
  have hc := activeBlockPrimes_card_le B (activePrimeAtoms B n)
  by_cases h : R ≤ (activeBlockPrimes B (activePrimeAtoms B n)).card
  · rw [if_pos h,if_pos (h.trans hc)]
    exact subsetPolynomial_mono k hc
  · rw [if_neg h]
    split_ifs
    · exact subsetPolynomial_nonneg _ _
    · rfl

/-- Products below B^k cannot delete more than k primes, all exceeding B.
This makes the cardinality cap redundant in the arithmetic application. -/
lemma short_prime_product_card_le (E : Finset ℕ) (B k : ℕ) (hB : 1 < B)
    (hE : ∀ p ∈ E, B < p) (hprod : (∏ p ∈ E, p) ≤ B^k) : E.card ≤ k := by
  have hpow : B^E.card ≤ ∏ p ∈ E, p := by
    simpa only [prod_const] using prod_le_prod' (fun p hp => (hE p hp).le)
  exact (Nat.pow_le_pow_iff_right hB).mp (hpow.trans hprod)

#print axioms short_prime_product_card_le
#print axioms clippedShortComplementPattern_arithmetic_error
end Erdos371.FiniteSieve
