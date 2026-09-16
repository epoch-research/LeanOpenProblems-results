import FormalConjectures.Util.ProblemImports
import Submission.Spec

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

def a_comp (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => Nat.Prime (n^2 - pi_fn_comp (k * n))) (Finset.Ico 1 n)).card

#eval (List.range 100).drop 2 |>.filter (fun n => a_comp n == 0)
