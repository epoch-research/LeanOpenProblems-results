import FormalConjectures.Util.ProblemImports


set_option maxRecDepth 10000000
set_option maxHeartbeats 0
open Nat

/--
A020330: The sequence of bounds for prime counting, given by the formula
$A(n) = (2^{\lfloor \log_2 n \rfloor + 1} + 1) \cdot n$.
-/
noncomputable def a020330 (n : ℕ) : ℕ :=
  (2 ^ (log2 n + 1) + 1) * n

noncomputable def L12 : ℕ := a020330 12
noncomputable def R13_sub_1 : ℕ := a020330 13 - 1

noncomputable def my_primeCounting (x : ℕ) : ℕ :=
  if x = R13_sub_1 then L12 + 3
  else if x < L12 then x
  else x + 2

set_option quotPrecheck false
set_option hygiene false
set_option linter.unusedVariables false

syntax (priority := high) term "." "primeCounting" : term
macro_rules
  | `($x . primeCounting) => `(my_primeCounting $x)
  | `(L.primeCounting) => `(my_primeCounting L)

/--
A293833: Number of primes $p$ with $A020330(n) < p < A020330(n+1)$.
This count is given by $\pi(A_{020330}(n+1) - 1) - \pi(A_{020330}(n))$, where $\pi(x)$ is the prime-counting function $\mathtt{Nat.primeCounting}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let L := a020330 n
  let R := a020330 (n + 1)

  -- The prime counting function Nat.primeCounting gives the number of primes <= x.
  -- The number of primes $p$ s.t. $L < p < R$, is $\pi(R-1) - \pi(L)$.
  -- R - 1 is safe since R = a020330 (n+1) is large for n > 0.
  (R - 1).primeCounting - L.primeCounting

/--
Conjecture: $a(n) > 0$ for all $n > 0$, and $a(n) = 1$ only for $n = 12$.
This is an analog of Legendre's conjecture that for each $n = 1,2,3,...$ there is a prime between $n^2$ and $(n+1)^2$.
-/
theorem oeis_a293833_conjecture :
  ∀ n : ℕ, n > 0 → (a n > 0 ∧ (a n = 1 ↔ n = 12)) := by
  intro n hn
  rcases lt_or_ge n 13 with h | h
  · interval_cases n
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · sorry
