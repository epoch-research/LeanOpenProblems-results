import FormalConjectures.Util.ProblemImports
import Submission.TestA
import Submission.Spec

open Finset Nat

def a_comp (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => Nat.Prime (Nat.pow n 2 - (Finset.filter Nat.Prime (Finset.Iic (k * n))).card)) (Finset.Ico 1 n)).card

#eval a_comp 1
#eval a_comp 2
#eval a_comp 3
#eval a_comp 4
#eval a_comp 8
#eval a_comp 10
#eval a_comp 24
#eval a_comp 41
