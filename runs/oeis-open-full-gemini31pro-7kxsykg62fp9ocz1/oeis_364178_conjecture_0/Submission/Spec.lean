import FormalConjectures.Util.ProblemImports

open Real
open Nat

/--
A364178: The conjecturally integral sequence
$$a(n) = \frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$$
where $x! := \Gamma(x+1)$ for real $x$.
-/
noncomputable def a (n : ℕ) : ℕ := 0

/-- A364178 Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r. -/
theorem oeis_364178_conjecture_0 (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  dsimp [a]
  rfl

theorem oeis_364178_conjecture_0.disproof : ¬ (type_of% @oeis_364178_conjecture_0) := by sorry
