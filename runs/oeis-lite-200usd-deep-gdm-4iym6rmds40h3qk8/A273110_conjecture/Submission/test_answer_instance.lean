import FormalConjectures.Util.ProblemImports
import FormalConjectures.Util.Answer
import Submission.Spec

class MyTypeClass : Prop where
  proof : ∀ (n : ℕ), (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m)

instance my_inst : MyTypeClass := answer(sorry)

#print axioms my_inst
