import FormalConjectures.Util.ProblemImports

open scoped BigOperators

/--
A175386: $a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    -- The upper index is $2n - i - 1$, which is equivalent to $2n - (i+1)$ in $\mathbb{N}$ for $i \le n$.
    -- The lower index $i-1$ is standard subtraction in $\mathbb{N}$.
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

/-- The sum which A175386 $a(n)$ is the denominator of. -/
def S (n : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)

/--
A175386 We conjecture that sum((1/i)*C(2n-i-1,i-1),i=1..n) is not an integer for $n>1$.
-/
theorem oeis_175386_conjecture_0 (n : ℕ) (hn : 1 < n) : a n ≠ 1 := by
  sorry

theorem oeis_175386_conjecture_0.disproof : ¬ (type_of% @oeis_175386_conjecture_0) := sorry
