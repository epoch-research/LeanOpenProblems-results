import Mathlib

open Nat

def a_comp (n : ℕ) : ℕ :=
  let candidates : Finset ℕ :=
    (Finset.range (6 * n + 3)).filter (fun p =>
      p.Prime ∧
      (p - 2).Prime ∧
      (6 * n - p).Prime ∧
      (6 * n + 2 - p).Prime)
  match candidates.min with
  | Option.some p_min => p_min
  | Option.none   => 0

#eval (List.range 200).filter (fun n => a_comp n = 0)
