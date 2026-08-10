import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  let candidates : Finset ℕ :=
    (Finset.range (6 * n + 3)).filter (fun p =>
      p.Prime ∧
      (p - 2).Prime ∧
      (6 * n - p).Prime ∧
      (6 * n + 2 - p).Prime)

  -- Finset.min returns an Option ℕ. We return the minimum if present, or 0 otherwise.
  match candidates.min with
  | Option.some p_min => p_min
  | Option.none   => 0

theorem a_16 : a 16 = 0 := by
  decide















