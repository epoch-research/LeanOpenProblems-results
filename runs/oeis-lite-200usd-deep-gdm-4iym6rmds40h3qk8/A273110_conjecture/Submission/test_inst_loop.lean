import FormalConjectures.Util.ProblemImports
import Submission.Spec

instance my_inst : Inhabited (Nonempty (∀ n, (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k m, m ∈ A273110_set_M ∧ n = 4 ^ k * m))) where
  default := my_inst.default

#print axioms my_inst
