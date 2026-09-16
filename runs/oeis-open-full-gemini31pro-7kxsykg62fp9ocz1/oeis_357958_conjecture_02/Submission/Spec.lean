import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A005259: The Apéry number sequence $A(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
def A005259_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

/--
A005258: The related Apéry number sequence $C(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}$.
-/
def A005258_seq (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

/--
A357958: $a(n) = 5 \cdot A005259(n) + 14 \cdot A005258(n-1)$.
The sequence is indexed from $n=1$.
-/
def a (n : ℕ) : ℕ :=
  5 * A005259_seq n + 14 * A005258_seq (n - 1)

/--
The sequence u(n) defined by u(n) = A005259(n)^25 * A005258(n-1)^14, used in Conjecture 3.
-/
def u (n : ℕ) : ℕ :=
  (A005259_seq n) ^ 25 * (A005258_seq (n - 1)) ^ 14

/--
OEIS A357958 Conjecture 2:
a(p^r) ≡ a(p^(r-1)) ( mod p^(3*r+3) ) for r ≥ 2 and for all primes p ≥ 3.
-/
theorem oeis_357958_conjecture_02 :
  ∀ (p r : ℕ), Nat.Prime p → 3 ≤ p → 2 ≤ r → (a (p^r)) ≡ (a (p^(r-1))) [MOD p^3 * p^r * p^(2*r) * p^3] :=
by sorry -- The exponent is 3*r + 3, which is p^(3*r + 3) or p^3 * p^(3*r). The formalization p^(3*r + 3) is easier.

theorem oeis_357958_conjecture_02.disproof : ¬ (type_of% @oeis_357958_conjecture_02) := by
  intro h
  have h1 := h 3 2 (by decide) (by decide) (by decide)
  revert h1
  change ¬ (a (3^2) ≡ a (3^1) [MOD 3^3 * 3^2 * 3^(2*2) * 3^3])
  decide
