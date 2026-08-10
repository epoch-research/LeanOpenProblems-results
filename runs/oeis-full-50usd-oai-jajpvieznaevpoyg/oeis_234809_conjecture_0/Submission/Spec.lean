import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A234809: $a(n) = |\{0 < k < n: p = k + \phi(n-k) \text{ and } 2(n-p) + 1 \text{ are both prime}\}|$,
where $\phi(\cdot)$ is Euler's totient function.
-/
noncomputable def A234809 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k : ℕ =>
    let p : ℕ := k + Nat.totient (n - k)
    if Nat.Prime p ∧ Nat.Prime (2 * (n - p) + 1) then 1 else 0

/-- Conjecture: a(n) > 0 for all n > 2. -/
theorem oeis_234809_conjecture_0 (n : ℕ) (hn : n > 2) : A234809 n > 0 :=
  by sorry
