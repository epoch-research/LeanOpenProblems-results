import FormalConjectures.Util.ProblemImports

open Nat Finset


/--
A357960: $a(n) = A005259(n-1)^5 \cdot A005258(n)^6$.
The sequence is defined by the combinatorial formula:
$$a(n) = \left( \sum_{k = 0}^{n-1} \binom{n-1}{k}^2 \binom{n+k-1}{k}^2 \right)^5 \cdot \left( \sum_{k = 0}^{n} \binom{n}{k}^2 \binom{n+k}{k} \right)^6$$
-/
def a (n : ℕ) : ℕ :=
  let N := n - 1
  ( (range n).sum fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2 ) ^ 5 *
  ( (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ) ^ 6

/--
Conjecture 1 from OEIS A357960:
$a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem oeis_A357960_conjecture_1 (p : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) :
    a p ≡ a 1 [MOD p ^ 5] := by
  sorry
