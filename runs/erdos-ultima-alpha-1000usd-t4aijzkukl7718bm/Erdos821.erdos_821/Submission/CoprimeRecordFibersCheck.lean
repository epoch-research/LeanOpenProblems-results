import Submission.CoprimeRecordFibers

/-! Exact-type and permitted-axiom audit of coprime record fibers. -/

open Nat Filter
open Erdos821 Erdos821.CoprimeRecords

example (s η : ℝ) (hs : 1/2 < s) (hη : 0 < η) :
    ∃ B : ℕ, ∀ n : ℕ, 0 < n →
      (∀ j : ℕ, j ≤ n → (gAvoiding B.factorial j : ℝ)/(j : ℝ)^s ≤
        (gAvoiding B.factorial n : ℝ)/(n : ℝ)^s) →
      (1-η)*(gAvoiding B.factorial n : ℝ)^2 ≤ (coprimePairs B.factorial n).card :=
  exists_cutoff_record_coprime_proportion s η hs hη

example (α η : ℝ) (hα : 1/2 < α)
    (hupper : α < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10))
    (hη : 0 < η) :
    ∃ B : ℕ, ∀ N : ℕ, ∃ n : ℕ, max N 1 < n ∧
      (n : ℝ)^α < (gAvoiding B.factorial n : ℝ) ∧
      (1-η)*(gAvoiding B.factorial n : ℝ)^2 ≤ (coprimePairs B.factorial n).card :=
  exists_large_mostly_coprime_records α η hα hupper hη

example (γ : ℝ) (hγ : 1/2 < γ)
    (hupper : γ < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)) :
    ∃ B : ℕ, {n : ℕ | 1 < n ∧
      (n : ℝ)^(2*γ) < ((coprimePairs B.factorial n).card : ℝ)}.Infinite :=
  infinite_large_primitive_pair_count γ hγ hupper

#print axioms card_avoidingFiber_dvd_le
#print axioms normalized_record_core_bound
#print axioms normalized_record_core_square_bound
#print axioms pair_card_partition
#print axioms noncoprime_gcd_gt_cutoff
#print axioms noncoprimePairs_le_core_sum
#print axioms noncoprimePairs_record_le
#print axioms exists_small_totient_tail
#print axioms exists_cutoff_record_coprime_proportion
#print axioms coprimePairs_distinct
#print axioms exists_large_mostly_coprime_records
#print axioms infinite_large_primitive_pair_count

example (K n : ℕ) (ab : ℕ × ℕ) (hab : ab ∈ coprimePairs K n) :
    ab.1*ab.2 ∈ avoidingFiber K (n^2) := coprimePair_product_mem K n ab hab
#print axioms coprimePair_product_mem
