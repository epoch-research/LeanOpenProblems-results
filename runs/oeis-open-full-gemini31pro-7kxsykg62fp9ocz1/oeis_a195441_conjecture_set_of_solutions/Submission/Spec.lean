import FormalConjectures.Util.ProblemImports

open Polynomial Rat Finset Nat UniqueFactorizationMonoid

noncomputable def A195441 (n : ℕ) : ℕ :=
  let N := n + 1
  let B_num : ℚ := _root_.bernoulli N
  let P : ℚ[X] := Polynomial.bernoulli N - C B_num
  (range (N + 1)).lcm fun k => (P.coeff k).den

theorem oeis_a195441_conjecture_set_of_solutions :
    { n : ℕ | 1 ≤ n ∧ A195441 (n - 1) = radical (n + 1) } =
    ({3, 5, 8, 9, 11, 27, 29, 35, 59} : Finset ℕ).toSet := by sorry

theorem oeis_a195441_conjecture_set_of_solutions.disproof : ¬ (type_of% @oeis_a195441_conjecture_set_of_solutions) := by sorry
