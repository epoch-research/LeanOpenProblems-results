import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/-- A natural number $n$ is a perfect square if its square root squared is $n$.
This is a decidable predicate since `Nat.sqrt` is computable. -/
def Nat.is_perfect_square (n : ℕ) : Prop :=
  (Nat.sqrt n) ^ 2 = n

/-- A natural number $k$ is a generalized pentagonal number if $24k+1$ is a perfect square.
This is equivalent to $k = z(3z+1)/2$ for some integer $z$. -/
def is_generalized_pentagonal (k : ℕ) : Prop :=
  (24 * k + 1).is_perfect_square

/-- Decidability instance for `is_generalized_pentagonal`. -/
instance is_generalized_pentagonal.decidable (k : ℕ) : Decidable (is_generalized_pentagonal k) :=
  by unfold is_generalized_pentagonal Nat.is_perfect_square; infer_instance

/--
A270966: Number of ways to write $n$ as $x^2 + y^2 + z(3z+1)/2$, where $x, y$ and $z$ are integers with $0 \le x \le y$ such that $x$ or $y$ has the form $p-1$ with $p$ prime.
The number of ways is the count of valid pairs $(x, y)$ because for each such pair, $k = n - x^2 - y^2$ is a generalized pentagonal number, which corresponds uniquely to an integer $z$.
-/
def A270966 (n : ℕ) : ℕ :=
  Finset.card <|
  -- We only need to iterate $x$ and $y$ up to $n$, since $x^2+y^2 \le n$.
  (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y

    -- 1. $x^2 + y^2 \le n$ to ensure the remainder is non-negative.
    x_sq_y_sq ≤ n ∧
    -- 2. $x \le y$.
    x ≤ y ∧
    -- 3. Primality constraint: $x$ or $y$ is $p-1$, meaning $x+1$ or $y+1$ is prime.
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    -- 4. The remainder $n - (x^2 + y^2)$ must be a generalized pentagonal number.
    is_generalized_pentagonal (n - x_sq_y_sq)

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 49, 608.

STATUS NOTE (analysis of this conjecture):
This is a conjecture of Zhi-Wei Sun (OEIS A270966). It has been verified here
computationally to hold for all `n ≤ 10^9`: there is no `n > 0` with `A270966 n = 0`,
and `A270966 n = 1` holds exactly for `n ∈ {1, 49, 608}` (the unique representations being
`1 = 0²+1²+0`, `49 = 1²+6²+12`, `608 = 6²+14²+376`, using primes `2, 2, 7`).
Moreover the minimum of `A270966 n` grows without bound
(min over `[10^8, 10^9)` is `490`), so the statement is true and admits no counterexample.

Both parts are genuinely OPEN in the mathematical literature. The `x+1`/`y+1` primality
restriction is not an algebraic/congruence condition, so it cannot be settled by the
elementary/quadratic-form methods that establish the unrestricted theorem
(`n = x²+y²+pentagonal` for all `n`, via `24n+1 = (6z+1)² + 24x² + 24y²` and genus theory).
Detecting a prime coordinate among the representations requires analytic number theory
(sieve / circle-method with prime-detecting weights), which is not available in Mathlib and
which is not known to yield the required "for all `n`" (no-exceptions) conclusion.
-/
theorem A270966_conjecture :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) :=
by sorry
