import FormalConjecturesUtil

/-!
A checked obstruction to the binary digit-moment construction, not a disproof of Erdős 773.
Bit positions are indexed starting at zero.
-/

namespace Erdos773

private def binaryMoment17 (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 17, if n.testBit j then j ^ k else 0

lemma binary_moment_candidate_counterexample :
    (∀ n ∈ ({73353, 54474, 78666, 46473} : Finset ℕ),
      (binaryMoment17 n 0, binaryMoment17 n 1, binaryMoment17 n 2) = (8, 68, 760)) ∧
    ¬ IsSidon ({73353 ^ 2, 54474 ^ 2, 78666 ^ 2, 46473 ^ 2} : Set ℕ) := by
  constructor
  · decide
  · intro h
    have he := h (73353 ^ 2) (by simp) (78666 ^ 2) (by simp)
      (54474 ^ 2) (by simp) (46473 ^ 2) (by simp) (by norm_num)
    norm_num at he

#print axioms binary_moment_candidate_counterexample

end Erdos773
