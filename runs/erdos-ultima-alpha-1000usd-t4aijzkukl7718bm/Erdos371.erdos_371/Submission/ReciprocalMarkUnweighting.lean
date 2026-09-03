import Submission.HighWinnerMarkCoverage

/-! Exact removal of divisor-mark multiplicity by a reciprocal-fiber weight.
No cancellation estimate for this new weight is assumed or proved. -/
namespace Erdos371.Kloosterman
open Finset

def unmarkedIndexCount (p : ℕ) (s : Bool) (N : ℕ) : ℕ :=
  ((range N).filter fun n => 0 < indexMarkMultiplicity p s n).card

noncomputable def reciprocalIndexMarkWeight (p : ℕ) (s : Bool) (ab : ℕ×ℕ) : ℝ :=
  1 / indexMarkMultiplicity p s (divisorMarkIndex s ab)

lemma sum_reciprocalIndexMarkWeight_fiber (p n : ℕ) (s : Bool) :
    (∑ ab ∈ indexMarks p s n, reciprocalIndexMarkWeight p s ab) =
      if 0 < indexMarkMultiplicity p s n then (1 : ℝ) else 0 := by
  have he : (∑ ab ∈ indexMarks p s n, reciprocalIndexMarkWeight p s ab) =
      (indexMarkMultiplicity p s n : ℝ) * (1 / indexMarkMultiplicity p s n) := by
    calc
      _ = ∑ _ab ∈ indexMarks p s n, (1 : ℝ) / indexMarkMultiplicity p s n := by
        apply sum_congr rfl
        intro ab hab
        unfold reciprocalIndexMarkWeight
        rw [(mem_filter.mp hab).2]
      _ = _ := by simp only [sum_const,nsmul_eq_mul,indexMarkMultiplicity]
  rw [he]
  by_cases hm : 0 < indexMarkMultiplicity p s n
  · rw [if_pos hm]
    have hz : (indexMarkMultiplicity p s n : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    exact mul_one_div_cancel hz
  · have hz : indexMarkMultiplicity p s n = 0 := by omega
    simp [hz]

/-- A weighted marked count is exactly the number of covered indices. -/
theorem sum_reciprocalIndexMarkWeight_eq_unmarkedIndexCount (p N : ℕ) (s : Bool) :
    (∑ ab ∈ (chosenDivisorMarks p s).filter (fun ab => divisorMarkIndex s ab < N),
      reciprocalIndexMarkWeight p s ab) = (unmarkedIndexCount p s N : ℝ) := by
  have he := sum_fiberwise_eq_sum_filter (chosenDivisorMarks p s) (range N)
    (divisorMarkIndex s) (reciprocalIndexMarkWeight p s)
  change (∑ n ∈ range N, ∑ ab ∈ indexMarks p s n, reciprocalIndexMarkWeight p s ab) = _ at he
  simp only [mem_range,sum_reciprocalIndexMarkWeight_fiber] at he
  rw [← he]
  simp [unmarkedIndexCount]

lemma indexMark_actual_comparison (p n : ℕ) (hp : p.Prime) (s : Bool)
    (ab : ℕ×ℕ) (hab : ab ∈ indexMarks p s n) :
    1 < n ∧ primeWinner n = p ∧
      decide (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) = s := by
  obtain ⟨hab,he⟩ := mem_filter.mp hab
  have hbounds : ab ∈ (Ico 2 p).product (Ico 1 p) := by
    cases s <;> exact (mem_filter.mp hab).1
  have ha := (mem_Ico.mp (mem_product.mp hbounds).1).1
  have hb := (mem_Ico.mp (mem_product.mp hbounds).2).1
  have hprod : 2 ≤ ab.1*ab.2 := by nlinarith
  cases s
  · have hs := fallDivisorMarks_actual_sign p hp ab hab
    change ab.1*ab.2-1 = n at he
    rw [he] at hs
    have hd : p ∣ n := by simpa only [he] using (mem_filter.mp hab).2
    have hpn : p ≤ n := Nat.le_of_dvd (by omega) hd
    refine ⟨by have := hp.two_le; omega,hs.2,?_⟩
    apply decide_eq_false
    intro h
    norm_num [factorSign,predicateSign,h] at hs
  · have hs := riseDivisorMarks_actual_sign p hp ab hab
    change ab.1*ab.2 = n at he
    rw [he] at hs
    refine ⟨by omega,hs.2,?_⟩
    apply decide_eq_true
    by_contra h
    norm_num [factorSign,predicateSign,h] at hs

/-- In the covered range, a positive multiplicity is equivalent to the actual
comparison with that winning prime and orientation. -/
lemma high_winner_multiplicity_pos_iff (p N n : ℕ) (hp : p.Prime) (s : Bool)
    (hnN : n < N) (hsize : N^2 < p^3) :
    0 < indexMarkMultiplicity p s n ↔
      1 < n ∧ primeWinner n = p ∧
        decide (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) = s := by
  constructor
  · intro h
    obtain ⟨ab,hab⟩ := card_pos.mp h
    exact indexMark_actual_comparison p n hp s ab hab
  · rintro ⟨hn,hw,hs⟩
    have h := high_winner_has_indexMark N n hn hnN (by rwa [hw])
    simpa only [hw,hs] using h

/-- Exact unweighted arithmetic count after reciprocal weighting. -/
theorem unmarkedIndexCount_eq_actual_count (p N : ℕ) (hp : p.Prime) (s : Bool)
    (hsize : N^2 < p^3) :
    unmarkedIndexCount p s N =
      ((Ico 2 N).filter fun n => primeWinner n = p ∧
        decide (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) = s).card := by
  unfold unmarkedIndexCount
  congr 1
  ext n
  by_cases hnN : n < N
  · simp only [mem_filter,mem_range,hnN,true_and,mem_Ico,and_true,
      high_winner_multiplicity_pos_iff p N n hp s hnN hsize]
    rw [show 1 < n ↔ 2 ≤ n by omega]
  · simp only [mem_filter,mem_range,hnN,false_and,mem_Ico,and_false]

/-- In the high-winner range, summing reciprocal multiplicities over marks
counts precisely the corresponding original indices. The arithmetic weight
here is not covered by the unweighted inverse-curve cancellation theorem. -/
theorem reciprocal_mark_count_eq_actual_count (p N : ℕ) (hp : p.Prime) (s : Bool)
    (hsize : N^2 < p^3) :
    (∑ ab ∈ (chosenDivisorMarks p s).filter (fun ab => divisorMarkIndex s ab < N),
      reciprocalIndexMarkWeight p s ab) =
      (((Ico 2 N).filter fun n => primeWinner n = p ∧
        decide (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)) = s).card : ℝ) := by
  rw [sum_reciprocalIndexMarkWeight_eq_unmarkedIndexCount,
    unmarkedIndexCount_eq_actual_count p N hp s hsize]

/-- Reciprocal multiplicity is not preserved by the marked reflection.
This is only a finite diagnostic, not an asymptotic obstruction theorem. -/
lemma reciprocal_weight_reflection_example :
    reciprocalIndexMarkWeight 7 true (2,3) = (1 : ℝ)/3 ∧
      reciprocalIndexMarkWeight 7 false (reflectDivisorMark 7 (2,3)) = (1 : ℝ)/2 := by
  have h₁ : indexMarkMultiplicity 7 true 6 = 3 := by decide +kernel
  have h₂ : indexMarkMultiplicity 7 false 7 = 2 := by decide +kernel
  constructor
  · change (1 : ℝ)/indexMarkMultiplicity 7 true 6 = _
    rw [h₁]
    norm_num
  · change (1 : ℝ)/indexMarkMultiplicity 7 false 7 = _
    rw [h₂]
    norm_num

#print axioms reciprocal_weight_reflection_example
#print axioms sum_reciprocalIndexMarkWeight_eq_unmarkedIndexCount
#print axioms high_winner_multiplicity_pos_iff
#print axioms reciprocal_mark_count_eq_actual_count
end Erdos371.Kloosterman
