import Mathlib

open Finset Nat

/--
A234246: $a(n) = \left|\left\{0 < k < n: k \cdot \phi(n-k) + 1 \text{ is a square}\right\}\right|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k =>
    let m := k * Nat.totient (n - k) + 1
    if Nat.sqrt m * Nat.sqrt m = m then 1 else 0

-- Define the set S of conjectured values for a(n)=1
def S : Finset ℕ := {4, 5, 8, 9, 12, 13, 24, 33, 49}

theorem oeis_a234246_conjecture_i :
  (∀ n : ℕ, 0 < n → (¬ (n ∣ 6) → a n > 0)) ∧
  (∀ n : ℕ, a n = 1 ↔ n ∈ S) :=
by sorry

