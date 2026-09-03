import Submission.SparsePredecessorSupport

/-! Independent axiom audit of the sparse-support extraction bounds. -/
#print axioms Erdos821.SparsePredecessors.predecessor_multiple_card_le
#print axioms Erdos821.SparsePredecessors.nonsmooth_card_le_support_reciprocal
#print axioms Erdos821.SparsePredecessors.nonsmooth_card_le_support_card
#print axioms Erdos821.SparsePredecessors.smooth_subfamily_card_lower

open scoped Classical
example (P Q : Finset ℕ) (X Y : ℕ) (hY : 0 < Y)
    (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ X)
    (hQ : ∀ p ∈ P, (p-1).primeFactors ⊆ Q)
    (hbudget : 2*(Q.card : ℝ)*X ≤ Y*P.card) :
    (P.card : ℝ)/2 ≤ (P.filter (fun p => p-1 ∈ Nat.smoothNumbers Y)).card := by
  have H := Erdos821.SparsePredecessors.smooth_subfamily_card_lower P Q X Y hY hP hQ
    (1/2) (by nlinarith only [hbudget])
  nlinarith only [H]
