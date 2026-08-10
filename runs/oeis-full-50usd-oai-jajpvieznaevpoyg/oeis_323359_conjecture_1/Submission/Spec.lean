import FormalConjectures.Util.ProblemImports

open Nat

/--
The auxiliary sequence $b(k)$ for A323359, where $b(1)=2$ and $b(k) = b(k-1) + \operatorname{lcm}(\lfloor\sqrt{k^3}\rfloor, b(k-1))$ for $k \ge 2$.
-/
def b : ℕ → ℕ
| 0 => 0
| 1 => 2
| k_plus_1 + 1 =>
  let k := k_plus_1 + 1
  let b_prev := b k_plus_1
  b_prev + Nat.lcm (Nat.sqrt (k ^ 3)) b_prev

/--
A323359: $a(n) = b(n+1)/b(n) - 1$, where $n>0$ and $b$ is the auxiliary sequence.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    (b (n + 1) / b n) - 1

/--
Conjecture 1 from OEIS A323359: This sequence consists only of 1's and primes.
-/
theorem oeis_323359_conjecture_1 :
  ∀ (n : ℕ), 0 < n → (a n = 1 ∨ Nat.Prime (a n)) := by
  sorry
