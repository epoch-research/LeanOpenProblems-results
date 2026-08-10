import FormalConjectures.Util.ProblemImports
import Submission.Spec

class MyTypeClass (n : ℕ) : Prop where
  proof : (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m)

instance my_inst (n : ℕ) : MyTypeClass n := answer(sorry)

#print my_inst
#print axioms my_inst
