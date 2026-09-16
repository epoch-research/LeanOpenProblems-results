import FormalConjectures.Util.ProblemImports
import Submission.Spec

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

def a_comp (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => Nat.Prime (n^2 - pi_fn_comp (k * n))) (Finset.Ico 1 n)).card

#eval a_comp 24
#eval a_comp 10
#eval a_comp 8
#eval a_comp 4
#eval a_comp 3
#eval a_comp 2
