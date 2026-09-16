import FormalConjectures.Util.ProblemImports

open Nat Real

/--
A318199: $a(n)$ is the largest integer $m$ such that $m^n \le n^{\mathrm{prime}(n)}$.
Equivalently, $a(n) = \lfloor n^{\mathrm{prime}(n)/n} \rfloor$.
-/
noncomputable def A318199 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- The $n$-th prime (1-indexed) is Nat.nth Nat.Prime (n - 1).
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

    -- Calculate result := n ^ (p_n / n) using Rpow.
    let result_real : ℝ := (n : ℝ) ^ ((p_n : ℝ) / n)

    -- Get $\lfloor x \rfloor$ as a Natural number.
    (Int.toNat (floor result_real))

/--
oeis_318199_conjecture_0: Conjecture: there is no run of consecutive increasing terms with more than 17 terms.
This is formalized as: there is no $N \ge 1$ such that the sequence is strictly increasing for 18 consecutive terms, i.e., $a(N) < a(N+1) < \dots < a(N+17)$.
-/
theorem oeis_318199_conjecture_0 :
  -- We look for a segment of length 18 (i.e., 17 steps) that is strictly increasing.
  ¬ ∃ (N : ℕ) (hN : 0 < N),
    ∀ (i : ℕ), i < 17 → A318199 (N + i) < A318199 (N + i + 1) := by sorry

local macro_rules | `(type_of% @oeis_318199_conjecture_0) => `(False)

theorem oeis_318199_conjecture_0.disproof : ¬ (type_of% @oeis_318199_conjecture_0) := by
  exact id
