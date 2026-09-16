import FormalConjectures.Util.ProblemImports
import Submission.Spec

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

#eval (List.range 41).drop 1 |>.filter (fun k => Nat.Prime (1681 - pi_fn_comp (k * 41)))
