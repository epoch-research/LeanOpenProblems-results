import FormalConjectures.Util.ProblemImports
import Submission.Spec

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

#eval pi_fn_comp 615
