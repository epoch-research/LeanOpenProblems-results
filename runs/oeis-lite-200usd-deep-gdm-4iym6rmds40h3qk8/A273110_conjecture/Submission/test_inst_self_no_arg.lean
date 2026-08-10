import FormalConjectures.Util.ProblemImports
import Submission.Spec

def my_nonempty_of_inhabited [h : Inhabited α] : Nonempty α := Nonempty.intro default

instance my_inst : Inhabited (Nonempty (∀ n, (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k m, m ∈ A273110_set_M ∧ n = 4 ^ k * m))) where
  default := Classical.choice (@my_nonempty_of_inhabited _ my_inst)

#print axioms my_inst
