import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

lemma pi_fn_eq_comp (n : ℕ) : pi_fn n = pi_fn_comp n := by
  sorry

def a_comp (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => Nat.Prime (n^2 - pi_fn_comp (k * n))) (Finset.Ico 1 n)).card

lemma a_eq_comp (n : ℕ) : a n = a_comp n := by
  sorry

#eval a_comp 42
