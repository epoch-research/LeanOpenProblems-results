import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Option

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

#eval a_comp 100
#eval a_comp 16
