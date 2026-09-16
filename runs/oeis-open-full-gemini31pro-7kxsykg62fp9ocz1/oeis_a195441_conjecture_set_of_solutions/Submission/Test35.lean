import FormalConjectures.Util.ProblemImports

open Polynomial Rat Finset Nat UniqueFactorizationMonoid

noncomputable def A195441 (n : ℕ) : ℕ :=
  let N := n + 1
  let B_num : ℚ := _root_.bernoulli N
  let P : ℚ[X] := Polynomial.bernoulli N - C B_num
  (range (N + 1)).lcm fun k => (P.coeff k).den

theorem a195441_2 : A195441 2 = 2 := by
  unfold A195441
  sorry
