import Submission.ShortComplementWitness

/-! Arithmetic complementary-index prefixes with an independent endpoint X.
They coincide with the previous short sum when X=B^k. -/
namespace Erdos371
open Finset FiniteSieve

noncomputable def untruncatedComplementPrefix (B X n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if e ≤ X then (ArithmeticFunction.moebius e : ℝ)*
        divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

noncomputable def complementPrefixAt (B D X n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if e ≤ X ∧ D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma untruncatedComplementPrefix_power (B k n : ℕ) :
    untruncatedComplementPrefix B (B^k) n=shortRoughComplement B k n := rfl

lemma rough_prefix_subset_restrict (B C k X n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hX : X ≤ B^k) (hC : B^k ≤ C) (f : Finset ℕ → ℝ) :
    (∑ E ∈ (roughRadical B (n*(n+1))).primeFactors.powerset,
      if (∏ p ∈ E, p) ≤ X then f E else 0) =
    ∑ E ∈ (activeBlockPrimes (largePrimeSet B C)
        (activePrimeAtoms (largePrimeSet B C) n)).powerset,
      if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ X then f E else 0 := by
  have h := rough_short_subset_restrict B C k n hB hn hC
    (fun E => if (∏ p ∈ E, p) ≤ X then f E else 0)
  have he (E : Finset ℕ) :
      (if (∏ p ∈ E, p) ≤ B^k then (if (∏ p ∈ E, p) ≤ X then f E else 0) else 0) =
      (if (∏ p ∈ E, p) ≤ X then f E else 0) := by
    by_cases hx : (∏ p ∈ E, p) ≤ X
    · rw [if_pos (hx.trans hX),if_pos hx]
    · simp [hx]
  have hf (E : Finset ℕ) :
      (if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ B^k then
        (if (∏ p ∈ E, p) ≤ X then f E else 0) else 0) =
      (if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ X then f E else 0) := by
    by_cases hx : (∏ p ∈ E, p) ≤ X
    · simp [hx,hx.trans hX]
    · simp [hx]
  simpa only [he,hf] using h

lemma untruncatedComplementPrefix_eq_block_sum (B C k X n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hX : X ≤ B^k) (hC : B^k ≤ C) :
    untruncatedComplementPrefix B X n =
      (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
        ∑ E ∈ (activeBlockPrimes (largePrimeSet B C)
            (activePrimeAtoms (largePrimeSet B C) n)).powerset,
          if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ X then
            (-1 : ℝ)^E.card*divisorSideColour n
              (roughRadical B (n*(n+1))/(∏ p ∈ E, p)) else 0 := by
  unfold untruncatedComplementPrefix
  congr 1
  have he := squarefree_moebius_sum_eq_powerset (roughRadical B (n*(n+1)))
    (roughRadical_squarefree B _) (fun e => if e ≤ X then divisorSideColour n (roughRadical B (n*(n+1))/e) else 0)
  simp only [mul_ite,mul_zero] at he
  rw [he]
  exact rough_prefix_subset_restrict B C k X n hB hn hX hC _

lemma untruncatedComplementPrefix_eq_pattern (B C k X n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hX : X ≤ B^k) (hC : B^k ≤ C)
    (hocc : k < (activeBlockPrimes (largePrimeSet B C)
      (activePrimeAtoms (largePrimeSet B C) n)).card) :
    untruncatedComplementPrefix B X n = fullRadicalParity n*
      naturalBlockParity (primesThrough B) n*
        shortComplementPattern (largePrimeSet B C) X k
          (activePrimeAtoms (largePrimeSet B C) n) := by
  rw [untruncatedComplementPrefix_eq_block_sum B C k X n hB hn hX hC,
    roughRadical_moebius_eq_fullParity B n hn]
  congr 1
  unfold shortComplementPattern
  apply sum_congr rfl
  intro E hE
  by_cases h : E.card ≤ k ∧ (∏ p ∈ E, p) ≤ X
  · rw [if_pos h,if_pos h]
    congr 1
    symm
    apply rough_complement_first_colour B C n hn E (mem_powerset.mp hE)
    apply nonempty_iff_ne_empty.mpr
    intro hemp
    have hc := card_sdiff_add_card_eq_card (mem_powerset.mp hE)
    rw [hemp,card_empty,zero_add] at hc
    omega
  · rw [if_neg h,if_neg h]

lemma untruncatedComplementPrefix_abs_le (B C k X n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hX : X ≤ B^k) (hC : B^k ≤ C) :
    |untruncatedComplementPrefix B X n| ≤
      subsetPolynomial k (activeBlockPrimes (largePrimeSet B C)
        (activePrimeAtoms (largePrimeSet B C) n)).card := by
  rw [untruncatedComplementPrefix_eq_block_sum B C k X n hB hn hX hC,abs_mul,
    roughRadical_moebius_abs,one_mul,subsetPolynomial_eq_powerset]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro E _
  by_cases hc : E.card ≤ k
  · rw [if_pos hc]
    split_ifs
    · rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,divisorSideColour_abs]
    · norm_num
  · rw [if_neg hc,if_neg (not_and_of_not_left _ hc),abs_zero]

lemma untruncatedComplementPrefix_zero (B X : ℕ) :
    untruncatedComplementPrefix B X 0=if 1 ≤ X then 1 else 0 := by
  simp [untruncatedComplementPrefix,roughRadical,divisorSideColour]

#print axioms untruncatedComplementPrefix_eq_pattern
end Erdos371
