import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A229969: Number of ways to write $n = x + y + z$ with $0 < x \le y \le z$ such that all the six
numbers $2x-1, 2y-1, 2z-1, 2xy-1, 2xz-1, 2yz-1$ are prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Icc 1 (n / 3)) fun x ↦
    Finset.sum (Icc x ((n - x) / 2)) fun y ↦
      let z := n - x - y

      if Nat.Prime (2 * x - 1) ∧ Nat.Prime (2 * y - 1) ∧ Nat.Prime (2 * z - 1) ∧
         Nat.Prime (2 * x * y - 1) ∧ Nat.Prime (2 * x * z - 1) ∧ Nat.Prime (2 * y * z - 1)
      then 1 else 0

/--
Conjecture: a(n) > 0 for all n > 5. Moreover, any integer n > 6 can be written
as x + y + z with x among 3, 4, 6, 10, 15 such that 2*y-1, 2*z-1, 2*x*y-1, 2*x*z-1, 2*y*z-1 are prime.
-/
theorem oeis_A229969_conjecture (n : ℕ) :
  (n > 5 → a n > 0) ∧
  (n > 6 → ∃ x y z : ℕ,
    x > 0 ∧ y > 0 ∧ z > 0 ∧      -- 0 < x, y, z
    x + y + z = n ∧
    x ≤ y ∧ y ≤ z ∧              -- x ≤ y ≤ z
    x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
    Nat.Prime (2 * x - 1) ∧ Nat.Prime (2 * y - 1) ∧ Nat.Prime (2 * z - 1) ∧
    Nat.Prime (2 * x * y - 1) ∧ Nat.Prime (2 * x * z - 1) ∧ Nat.Prime (2 * y * z - 1)) :=
by sorry

theorem oeis_A229969_conjecture.disproof : ¬ (type_of% @oeis_A229969_conjecture) := by
  intro h
  have h7 := h 7
  have h2_7 : 7 > 6 := by decide
  rcases (h7).2 h2_7 with ⟨x, y, z, hx, hy, hz, hsum, hxy, hyz, hx_in, _⟩
  have hx3 : x ≥ 3 := by
    simp only [mem_insert, mem_singleton] at hx_in
    rcases hx_in with rfl | rfl | rfl | rfl | rfl <;> decide
  omega

