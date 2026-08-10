import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A219791: Number of ways to write $n=x+y$ ($0<x \le y$) with $(xy)^2+1$ prime.
-/
def a (n : ℕ) : ℕ :=
  -- The range for $x$ is $1 \le x \le \lfloor n/2 \rfloor$.
  let valid_x_range := Finset.Icc 1 (n / 2)
  valid_x_range.filter (fun x : ℕ => Nat.Prime ((x * (n - x)) ^ 2 + 1)) |>.card

/-- Zhi-Wei Sun also made the following general conjecture: For any positive integer k, each sufficiently large integer n cna be written as x+y (x>0, y>0) with (xy)^{2^k}+1 prime.
-/
theorem oeis_219791_conjecture_2 :
  ∀ (k : ℕ), 0 < k →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime ((x * y) ^ (2^k) + 1) := by sorry
