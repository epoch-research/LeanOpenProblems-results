import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

def a_comp (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => Nat.Prime (n^2 - pi_fn_comp (k * n))) (Finset.Ico 1 n)).card

#eval a_comp 6
