import FormalConjectures.Util.ProblemImports

open Nat

/--
A278415: The sum $\sum_{k=0}^n \binom{n}{2k} \binom{n-k}{k}(-1)^k$.
-/
def A278415 (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦
    (Nat.choose n (2 * k) : ℤ) * (Nat.choose (n - k) k : ℤ) * ((-1 : ℤ) ^ k)

open Padic

/--
oeis_278415_conjecture_1: Conjecture: For any prime $p > 3$ and positive integer $n$, the number $(A278415(p \cdot n) - A278415(n))/(p \cdot n)^2$ is always a $p$-adic integer.
-/
theorem oeis_278415_conjecture_1 (p : ℕ) [hp_prime : Fact p.Prime] (hp_gt_3 : p > 3) (n : ℕ) (hn_pos : 0 < n) :
    (by exact ((Int.cast (A278415 (p * n)) - Int.cast (A278415 n)) / (Nat.cast (p * n) : Padic p) ^ 2) ∈ PadicInt.subring p) :=
  by sorry
