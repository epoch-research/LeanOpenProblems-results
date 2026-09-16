import FormalConjectures.Util.ProblemImports
import Submission.Spec

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

def a_comp (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => Nat.Prime (n^2 - pi_fn_comp (k * n))) (Finset.Ico 1 n)).card

def in_special (n : ℕ) : Bool :=
  n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 8 ∨ n = 10 ∨ n = 24 ∨ n = 41

#eval (List.range 200).filter (fun n => n > 1 ∧ a_comp n = 1 ∧ !in_special n)
