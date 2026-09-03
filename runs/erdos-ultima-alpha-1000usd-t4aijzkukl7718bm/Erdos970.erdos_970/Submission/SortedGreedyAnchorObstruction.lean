import Submission.GreedyCoverOrder

/-! An increasing prime order need not choose an anchor below the next prime.
This finite obstruction does not concern the quadratic Jacobsthal conjecture. -/
namespace Erdos970.GreedyCoverOrder

private def anchorPrefix : List ℕ :=
  [2, 3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem anchorPrefix_certificate :
    anchorPrefix.Pairwise (· < ·) ∧
    (∀ p ∈ anchorPrefix, p.Prime ∧ p < 47) ∧
    firstPosition (greedyResidual (Finset.range 52) anchorPrefix) = 51 := by
  decide +kernel

/-- Strictly increasing primes can select a first uncovered position greater
than the next prime. The missing prime 11 matters in this example. -/
theorem exists_sorted_anchor_above_prime :
    ∃ l : List ℕ, ∃ p : ℕ,
      (l ++ [p]).Pairwise (· < ·) ∧
      (∀ q ∈ l ++ [p], q.Prime) ∧
      p < firstPosition (greedyResidual (Finset.range 52) l) := by
  obtain ⟨hs, hp, ha⟩ := anchorPrefix_certificate
  refine ⟨anchorPrefix, 47, ?_, ?_, ?_⟩
  · apply List.pairwise_append.mpr
    exact ⟨hs, by simp, by simpa using fun q hq => (hp q hq).2⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact (hp q hq).1
    · have hq47 : q = 47 := by simpa using hq
      subst q
      norm_num
  · rw [ha]
    omega

#print axioms exists_sorted_anchor_above_prime
end Erdos970.GreedyCoverOrder
