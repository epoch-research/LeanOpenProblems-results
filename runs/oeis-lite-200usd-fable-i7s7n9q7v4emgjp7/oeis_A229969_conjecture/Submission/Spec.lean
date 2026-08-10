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
Disproof of the conjecture: for `n = 7 > 6`, any decomposition `x + y + z = 7` with
`x ≤ y ≤ z` and `x ∈ {3, 4, 6, 10, 15}` would require `x + y + z ≥ 3 * x ≥ 9 > 7`,
a contradiction.
-/
theorem oeis_A229969_conjecture.disproof : ¬ ∀ (n : ℕ),
  (n > 5 → a n > 0) ∧
  (n > 6 → ∃ x y z : ℕ,
    x > 0 ∧ y > 0 ∧ z > 0 ∧      -- 0 < x, y, z
    x + y + z = n ∧
    x ≤ y ∧ y ≤ z ∧              -- x ≤ y ≤ z
    x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
    Nat.Prime (2 * x - 1) ∧ Nat.Prime (2 * y - 1) ∧ Nat.Prime (2 * z - 1) ∧
    Nat.Prime (2 * x * y - 1) ∧ Nat.Prime (2 * x * z - 1) ∧ Nat.Prime (2 * y * z - 1)) := by
  intro h
  obtain ⟨x, y, z, hx, hy, hz, hsum, hxy, hyz, hxmem, -⟩ := (h 7).2 (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
  omega
