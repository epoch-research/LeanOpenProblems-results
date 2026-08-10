import FormalConjectures.Util.ProblemImports

open Nat Set ArithmeticFunction


/--
A076495: Smallest $x$ such that $\sigma(x) \bmod x = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A076495 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x ≠ 0 ∧ (sigma 1 x) % x = n }


/--
A076495 At present, the 0 entry for n=5 is only a conjecture.
That is, it is conjectured that there is no positive natural number $x$ such that
$\sigma_1(x) \bmod x = 5$.
-/
theorem oeis_76495_conjecture_0 : A076495 5 = 0 := by sorry
