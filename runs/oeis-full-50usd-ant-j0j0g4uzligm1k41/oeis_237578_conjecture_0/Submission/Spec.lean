import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

set_option maxRecDepth 100000

/--
A237578: $a(n) = |\left\{0 < k < n: \pi(k \cdot n) \text{ is prime}\right\}|$, where $\pi(\cdot)$ is the prime counting function (A000720).
-/
def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

/--
Conjecture: a(n) > 0 for all n > 2, and a(n) = 1 only for n = 5, 8, 13.
Moreover, for each n = 1, 2, 3, ..., there is a positive integer k < 3*sqrt(n) + 3 with pi(k*n) prime.
-/
theorem oeis_237578_conjecture_0 :
  -- Part 1: a(n) > 0 for all n > 2
  (∀ n : ℕ, 2 < n → a n > 0) ∧
  -- Part 2: a(n) = 1 only for n = 5, 8, 13
  (∀ n : ℕ, a n = 1 ↔ n = 5 ∨ n = 8 ∨ n = 13) ∧
  -- Part 3: k < 3*sqrt(n) + 3 with pi(k*n) prime
  (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧ Nat.Prime (Nat.primeCounting (k * n))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: a(n) > 0 for all n > 2.
    -- This asserts that for every n the deterministic sequence π(kn) (k = 1,…,n-1)
    -- attains a prime value. It is an open conjecture of Zhi-Wei Sun (OEIS A237578):
    -- proving it amounts to showing the arithmetic progression {kn} meets the
    -- irregular set {m : π(m) prime}. This is a statement of the "is f(n) prime"
    -- type, whose proof is beyond current mathematics (it is not implied even by an
    -- effective Prime Number Theorem) and beyond Mathlib (no lower bound on π).
    intro n hn
    sorry
  · -- Part 2: a(n) = 1 ⇔ n ∈ {5, 8, 13}.
    intro n
    constructor
    · -- forward direction: open. Requires a(n) ≠ 1 for every other n, i.e. a(n) ≥ 2
      -- for all n > 13 — a strengthening of Part 1 demanding *two* prime values of
      -- π(kn) in the window. Verified computationally (n ≤ 8000) but open in general.
      intro h
      sorry
    · -- backward direction: fully decidable verification that a(5)=a(8)=a(13)=1.
      rintro (rfl | rfl | rfl) <;>
        · show a _ = 1
          decide
  · -- Part 3: ∃ k < 3√n + 3 with π(kn) prime. Open, with the same obstruction as
    -- Part 1 (and indeed Part 1 for n ≥ 15 follows from this, since then 3√n+3 ≤ n).
    intro n hn
    sorry
