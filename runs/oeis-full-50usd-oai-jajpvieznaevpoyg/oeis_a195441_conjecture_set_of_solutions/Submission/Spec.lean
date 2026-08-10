import FormalConjectures.Util.ProblemImports

open Polynomial Rat Finset Nat UniqueFactorizationMonoid

/--
A195441: $a(n) = \text{denominator}(\text{Bernoulli}_{n+1}(x) - \text{Bernoulli}_{n+1})$.
This is defined as the least common multiple of the denominators of the coefficients of the polynomial $\text{Bernoulli}_{n+1}(x) - \text{Bernoulli}_{n+1}$.
-/
noncomputable def A195441 (n : ℕ) : ℕ :=
  let N := n + 1
  -- The term `bernoulli N` here is the Bernoulli number $B_N \in \mathbb{Q}$.
  let B_num : ℚ := _root_.bernoulli N
  -- The polynomial $P(x) = B_N(x) - B_N$
  let P : ℚ[X] := Polynomial.bernoulli N - C B_num

  -- The polynomial P has degree N, so we check coefficients k from 0 to N.
  (range (N + 1)).lcm fun k => (P.coeff k).den

/--
A195441 The equation a(n-1) = denominator(Bernoulli_n(x) - Bernoulli_n) = rad(n+1) has only finitely many solutions, where rad(n) = A007947(n) is the radical of n.
It is conjectured that S = {3, 5, 8, 9, 11, 27, 29, 35, 59} is the full set of all such solutions.
Note that (S\{8})+1 joined with {1,2} equals A094960. More precisely, the set S implies the finite sequence of A094960.
See Kellner 2023. - _Bernd C. Kellner_, Oct 18 2023
-/
theorem oeis_a195441_conjecture_set_of_solutions :
    { n : ℕ | 1 ≤ n ∧ A195441 (n - 1) = radical (n + 1) } =
    ({3, 5, 8, 9, 11, 27, 29, 35, 59} : Finset ℕ).toSet := by sorry
