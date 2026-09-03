import Submission.BalancedSmoothFactorization
import Submission.InverseHyperbolaBoundary

/-! Coverage and exact multiplicity bookkeeping for divisor marks. Neither
coverage nor the identities below remove multiplicity from cancellation. -/
namespace Erdos371
open Finset

lemma rise_mark_exists_of_square_lt_cube (n p : ℕ) (hn : 1 < n)
    (hrise : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))
    (hw : primeWinner n = p) (hsize : n^2 < p^3) :
    ∃ ab ∈ riseDivisorMarks p, ab.1*ab.2 = n := by
  have hw' : Nat.maxPrimeFac (n+1) = p := (max_eq_right hrise.le).symm.trans hw
  have hmp : Nat.maxPrimeFac n < p := by rwa [← hw']
  obtain ⟨a,b,ha,hap,hb,hbp,he⟩ := exists_two_factors_lt_of_square_lt_cube n p hn hmp hsize
  refine ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ico.mpr ⟨ha,hap⟩,
    mem_Ico.mpr ⟨hb,hbp⟩⟩,?_⟩,he⟩
  change p ∣ a*b+1
  rw [he,← hw']
  exact Nat.maxPrimeFac_dvd

lemma fall_mark_exists_of_square_lt_cube (n p : ℕ) (hn : 1 < n)
    (hfall : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n)
    (hw : primeWinner n = p) (hsize : (n+1)^2 < p^3) :
    ∃ ab ∈ fallDivisorMarks p, ab.1*ab.2-1 = n := by
  have hw' : Nat.maxPrimeFac n = p := (max_eq_left hfall.le).symm.trans hw
  have hmp : Nat.maxPrimeFac (n+1) < p := by rwa [← hw']
  obtain ⟨a,b,ha,hap,hb,hbp,he⟩ := exists_two_factors_lt_of_square_lt_cube (n+1) p (by omega) hmp hsize
  have he' : a*b-1 = n := by omega
  refine ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ico.mpr ⟨ha,hap⟩,
    mem_Ico.mpr ⟨hb,hbp⟩⟩,?_⟩,he'⟩
  change p ∣ a*b-1
  rw [he',← hw']
  exact Nat.maxPrimeFac_dvd

namespace Kloosterman

def divisorMarkIndex (s : Bool) (ab : ℕ×ℕ) : ℕ :=
  if s then ab.1*ab.2 else ab.1*ab.2-1

def indexMarks (p : ℕ) (s : Bool) (n : ℕ) : Finset (ℕ×ℕ) :=
  (chosenDivisorMarks p s).filter fun ab => divisorMarkIndex s ab = n

def indexMarkMultiplicity (p : ℕ) (s : Bool) (n : ℕ) : ℕ :=
  (indexMarks p s n).card

/-- Exact sum of multiplicities, not a count of the underlying indices. -/
lemma markedIndexCount_eq_sum_multiplicities (p N : ℕ) (s : Bool) :
    markedIndexCount p s N = ∑ n ∈ range N, indexMarkMultiplicity p s n := by
  symm
  have he := sum_card_fiberwise_eq_card_filter (chosenDivisorMarks p s)
    (range N) (divisorMarkIndex s)
  simpa only [indexMarkMultiplicity,indexMarks,mem_range,divisorMarkIndex,markedIndexCount] using he

/-- Every comparison in a prefix is covered when its winning prime satisfies
N^2<p^3. Multiplicity may still vary with the index. -/
theorem high_winner_has_indexMark (N n : ℕ) (hn : 1 < n) (hnN : n < N)
    (hsize : N^2 < (primeWinner n)^3) :
    0 < indexMarkMultiplicity (primeWinner n)
      (decide (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))) n := by
  apply card_pos.mpr
  by_cases hrise : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · simp only [decide_eq_true hrise]
    obtain ⟨ab,hab,he⟩ := rise_mark_exists_of_square_lt_cube n (primeWinner n) hn hrise rfl
      ((Nat.pow_le_pow_left hnN.le 2).trans_lt hsize)
    exact ⟨ab,mem_filter.mpr ⟨hab,he⟩⟩
  · simp only [decide_eq_false hrise]
    have hfall : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n :=
      lt_of_le_of_ne (not_lt.mp hrise) (consecutive_maxPrimeFac_ne n)
    obtain ⟨ab,hab,he⟩ := fall_mark_exists_of_square_lt_cube n (primeWinner n) hn hfall rfl
      ((Nat.pow_le_pow_left (by omega : n+1 ≤ N) 2).trans_lt hsize)
    exact ⟨ab,mem_filter.mpr ⟨hab,he⟩⟩

/-- A concrete uncovered comparison outside the coverage range. -/
lemma rise_twenty_seven_unmarked :
    primeWinner 27 = 7 ∧ factorSign 27 = 1 ∧ indexMarkMultiplicity 7 true 27 = 0 := by
  have h : Nat.maxPrimeFac 27 = 3 ∧ Nat.maxPrimeFac 28 = 7 := by decide +kernel
  refine ⟨?_,?_,by decide +kernel⟩
  · norm_num [primeWinner,h.1,h.2]
  · norm_num [factorSign,predicateSign,h.1,h.2]

/-- Covered indices need not have equal multiplicities. -/
lemma unequal_indexMark_multiplicities :
    indexMarkMultiplicity 7 true 6 = 3 ∧ indexMarkMultiplicity 7 true 20 = 2 := by
  decide +kernel

#print axioms markedIndexCount_eq_sum_multiplicities
#print axioms high_winner_has_indexMark
#print axioms rise_twenty_seven_unmarked
#print axioms unequal_indexMark_multiplicities
end Kloosterman
#print axioms rise_mark_exists_of_square_lt_cube
#print axioms fall_mark_exists_of_square_lt_cube
end Erdos371
