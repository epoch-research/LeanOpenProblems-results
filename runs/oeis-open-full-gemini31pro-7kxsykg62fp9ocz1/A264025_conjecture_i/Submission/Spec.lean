import FormalConjectures.Util.ProblemImports

open Nat

/--
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem A264025_conjecture_i :
  (∀ (n : ℕ), n > 0 → A264025 n > 0) ∧
  (∀ (n : ℕ), A264025 n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ)) := by
  sorry

theorem A264025_conjecture_i.disproof : ¬ (type_of% @A264025_conjecture_i) := sorry
