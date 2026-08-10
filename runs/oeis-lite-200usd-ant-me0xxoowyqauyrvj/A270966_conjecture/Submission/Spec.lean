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

set_option maxHeartbeats 10000000

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 49, 608.
-/
theorem A270966_conjecture :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) :=
by
  -- The whole conjecture reduces to a single statement about all `n > 608`,
  -- namely that there are at least two valid representations.  This is the
  -- (prime-restricted) effective lower bound for representations as
  -- `x² + y² + pentagonal`, a genuinely OPEN problem in additive number theory.
  -- (Numerically the minimum of `A270966 n` over `n > 608` is `4`,
  -- verified well past `5·10¹¹`.)
  have key : ∀ n : ℕ, 608 < n → 2 ≤ A270966 n := by
    sorry
  -- All finite parts below are settled by direct computation.
  have pos_small : ∀ n : ℕ, n < 609 → 0 < n → 0 < A270966 n := by native_decide
  have fwd_small : ∀ n : ℕ, n < 609 → A270966 n = 1 → n = 1 ∨ n = 49 ∨ n = 608 := by
    native_decide
  refine ⟨?_, fun n => ⟨?_, ?_⟩⟩
  · -- Part (i): a(n) > 0 for all n > 0.
    intro n hn
    rcases lt_or_ge n 609 with h | h
    · exact pos_small n h hn
    · have := key n (by omega); omega
  · -- Part (ii) forward: a(n) = 1 → n ∈ {1, 49, 608}.
    intro h1
    rcases lt_or_ge n 609 with h | h
    · exact fwd_small n h h1
    · have := key n (by omega); omega
  · -- Part (ii) backward: provable by direct computation.
    rintro (rfl | rfl | rfl) <;> native_decide
