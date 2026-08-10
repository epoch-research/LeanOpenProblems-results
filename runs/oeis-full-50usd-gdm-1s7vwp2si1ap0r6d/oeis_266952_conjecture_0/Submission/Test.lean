import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  let candidates : Finset ℕ :=
    (Finset.range (6 * n + 3)).filter (fun p =>
      p.Prime ∧
      (p - 2).Prime ∧
      (6 * n - p).Prime ∧
      (6 * n + 2 - p).Prime)

  match candidates.min with
  | Option.some p_min => p_min
  | Option.none   => 0

set_option google.answer "with_auxiliary"

theorem oeis_266952_conjecture_0 : Set.Finite {n : ℕ | a n = 0} := by
  exact answer(sorry)

#print axioms oeis_266952_conjecture_0



