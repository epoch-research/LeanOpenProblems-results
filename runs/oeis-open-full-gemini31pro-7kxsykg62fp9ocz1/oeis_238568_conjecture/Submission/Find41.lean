import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

def pi_fn_comp (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

def is_prime_bool (n : ℕ) : Bool :=
  n.Prime

#eval (List.range 41).drop 1 |>.map (fun k => (k, 1681 - pi_fn_comp (k * 41), is_prime_bool (1681 - pi_fn_comp (k * 41))))
