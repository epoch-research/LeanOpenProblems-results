import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A212334: Number of words, either empty or beginning with the first letter of the 4-ary alphabet,
where each letter of the alphabet occurs $n$ times and letters of neighboring word
positions are equal or neighbors in the alphabet.

The sequence is defined by the identity
$$a(n) = \sum_{k=0}^{n-1} \binom{n}{k} \binom{n-1}{k} \binom{n+k-1}{k}^2 \text{ for } n \ge 1$$
and $a(0) = 1$.
-/
def A212334 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (Finset.range n) fun k =>
      (n.choose k) * ((n - 1).choose k) * ((n + k - 1).choose k) ^ 2

theorem oeis_212334_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (h_ge5 : 5 ≤ p) (h_ge2 : 2 ≤ r) :
    A212334 (p ^ r) % (p ^ (3 * r + 3)) = A212334 (p ^ (r - 1)) % (p ^ (3 * r + 3)) := by
  sorry
