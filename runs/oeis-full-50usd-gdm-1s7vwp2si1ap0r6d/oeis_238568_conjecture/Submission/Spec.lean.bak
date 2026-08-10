import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The prime counting function $\pi(x)$, which computes the number of primes less than or equal to $x$.
We define it noncomputably since primality testing on $\mathbb{N}$ requires external resources like `prime_coalition`.
-/
noncomputable def pi_fn (n : ℕ) : ℕ :=
  Nat.card {p // Nat.Prime p ∧ p ≤ n}

/--
A238568: $a(n) = |\left\{ 0 < k < n: n^2 - \pi(k \cdot n) \text{ is prime} \right\}|$.
The sequence counts the number of $k \in \{1, \dots, n-1\}$ for which $n^2 - \pi(kn)$ is prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun k : ℕ =>
    Nat.Prime (Nat.pow n 2 - pi_fn (k * n))
  ) (Finset.Ico 1 n)

/-- The set of integers $n$ for which $a(n)=1$ according to the conjecture. -/
def A238568_special_set : Set ℕ := {2, 3, 4, 8, 10, 24, 41}

/--
Conjecture from OEIS A238568:
(i) $a(n) > 0$ for all $n > 1$.
(ii) $a(n) = 1$ if and only if $n \in \{2, 3, 4, 8, 10, 24, 41\}$.
-/
theorem oeis_238568_conjecture :
  (∀ (n : ℕ), 1 < n → 0 < a n) ∧
  (∀ (n : ℕ), a n = 1 ↔ n ∈ A238568_special_set) :=
by sorry
