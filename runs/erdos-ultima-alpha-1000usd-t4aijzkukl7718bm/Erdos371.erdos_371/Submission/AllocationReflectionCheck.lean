import Submission.ComparisonTupleExpansion

/-! A check on direct reflection of the new allocation weights. This is an
obstruction to a proposed pointwise pairing, not a disproof of the conjecture. -/
namespace Erdos371
open Finset RandomBins

namespace RandomBins
/-- The number of whole-prime-power allocations with integral box cutoff. -/
def primeAllocationCount (K B n : ℕ) : ℕ :=
  (univ.filter (fun a : PrimeAtomIndex n → Fin K =>
    ∀ c, boxProduct (primePowerAtom n) a c ≤ B)).card

lemma primeAllocationRetention_nat_eq_count (K B n : ℕ) :
    primeAllocationRetention K B n =
      (primeAllocationCount K B n : ℝ) * ((K : ℝ)⁻¹)^n.primeFactors.card := by
  classical
  unfold primeAllocationRetention
  have hweight (a : PrimeAtomIndex n → Fin K) :
      (∏ c, allocationWeight K (boxProduct (primePowerAtom n) a c)) =
        ((K : ℝ)⁻¹)^n.primeFactors.card := by
    simpa only [Fintype.card_coe] using
      prod_allocationWeight_boxes K (fun i : PrimeAtomIndex n => i.val)
        (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)
        Subtype.val_injective a
  simp_rw [hweight,Nat.cast_le]
  simp only [sum_const,nsmul_eq_mul,primeAllocationCount]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma primeAllocationCounts_14 :
    primeAllocationCount 2 14 77 = 2 ∧
    primeAllocationCount 2 14 66 = 2 ∧
    primeAllocationCount 2 14 6 = 4 ∧
    primeAllocationCount 2 14 5 = 2 := by
  simp only [primeAllocationCount,boxProduct,primePowerAtom,← Nat.primeFactorsList_count_eq]
  decide +kernel

lemma primeAllocationRetention_14 :
    primeAllocationRetention 2 14 77 = (1/2 : ℝ) ∧
    primeAllocationRetention 2 14 66 = (1/4 : ℝ) ∧
    primeAllocationRetention 2 14 6 = 1 ∧
    primeAllocationRetention 2 14 5 = 1 := by
  obtain ⟨h77,h66,h6,h5⟩ := primeAllocationCounts_14
  have hcards : (77 : ℕ).primeFactors.card = 2 ∧ (66 : ℕ).primeFactors.card = 3 ∧
      (6 : ℕ).primeFactors.card = 2 ∧ (5 : ℕ).primeFactors.card = 1 := by decide +kernel
  simp only [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num,
    primeAllocationRetention_nat_eq_count,h77,h66,h6,h5,
    hcards.1,hcards.2.1,hcards.2.2.1,hcards.2.2.2]
  norm_num
end RandomBins

/-- Both reflected pairs are genuine comparisons with winner 13, and both
losing-side factorizations are coprime. -/
lemma allocation_reflection_arithmetic :
    Nat.maxPrimeFac 77 = 11 ∧ Nat.maxPrimeFac 78 = 13 ∧
    Nat.maxPrimeFac 65 = 13 ∧ Nat.maxPrimeFac 66 = 11 ∧
    (11 : ℕ).Coprime 7 ∧ (11 : ℕ).Coprime 6 ∧
    11*7+1 = 13*6 ∧ 11*(13-7)-1 = 13*5 := by
  decide +kernel

/-- A strictly positive inflation that makes the common box cutoff 14. -/
noncomputable def reflectionInflation : ℝ := Real.log (14/13) / Real.log 78

lemma reflectionInflation_pos : 0 < reflectionInflation :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

lemma reflectionInflation_cutoff : (13 : ℝ)*78^reflectionInflation = 14 := by
  unfold reflectionInflation
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 78)]
  have hlog : Real.log 78 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 78)).ne'
  rw [mul_div_cancel₀ _ hlog,Real.exp_log (by norm_num : (0 : ℝ) < 14/13)]
  norm_num

/-- This reflection changes the complete retained fiber weight, even after
normalizing all assignments and including the winning-cofactor retention. -/
theorem comparisonAllocationWeight_reflection_check :
    comparisonAllocationWeight 2 78 reflectionInflation 77 = (1/2 : ℝ) ∧
    comparisonAllocationWeight 2 78 reflectionInflation 65 = (1/4 : ℝ) ∧
    factorSign 77 = 1 ∧ factorSign 65 = -1 := by
  obtain ⟨hp77,hp78,hp65,hp66,hrest⟩ := allocation_reflection_arithmetic
  obtain ⟨h77,h66,h6,h5⟩ := primeAllocationRetention_14
  norm_num [comparisonAllocationWeight,primeWinner,losingNumber,winningNumber,
    factorSign,predicateSign,hp77,hp78,hp65,hp66,h77,h66,h6,h5,reflectionInflation_cutoff]

/-- Consequently this particular pair does not cancel with the new weights. -/
theorem comparisonAllocation_reflected_pair_not_cancel :
    factorSign 77 * comparisonAllocationWeight 2 78 reflectionInflation 77 +
      factorSign 65 * comparisonAllocationWeight 2 78 reflectionInflation 65 = (1/4 : ℝ) := by
  obtain ⟨h77,h65,hs77,hs65⟩ := comparisonAllocationWeight_reflection_check
  rw [h77,h65,hs77,hs65]
  norm_num

#print axioms primeAllocationCounts_14
#print axioms comparisonAllocationWeight_reflection_check
#print axioms comparisonAllocation_reflected_pair_not_cancel
end Erdos371
