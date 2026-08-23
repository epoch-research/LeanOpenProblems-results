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
The formalized statement is false already for `n = 7`: the second conjunct requires
`x ∈ {3, 4, 6, 10, 15}` and `x ≤ y ≤ z` with `x + y + z = 7`, which forces `3 * x ≤ 7`.
-/
theorem oeis_A229969_conjecture.disproof :
    ¬∀ (n : ℕ),
      (n > 5 → a n > 0) ∧
      (n > 6 →
        ∃ x y z : ℕ,
          x > 0 ∧ y > 0 ∧ z > 0 ∧
          x + y + z = n ∧
          x ≤ y ∧ y ≤ z ∧
          x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
          Nat.Prime (2 * x - 1) ∧ Nat.Prime (2 * y - 1) ∧ Nat.Prime (2 * z - 1) ∧
          Nat.Prime (2 * x * y - 1) ∧ Nat.Prime (2 * x * z - 1) ∧ Nat.Prime (2 * y * z - 1)) := by
  intro h
  obtain ⟨_, h7⟩ := h 7
  obtain ⟨x, y, z, _hx, _hy, _hz, hsum, hxy, hyz, hxmem, _⟩ := h7 (by decide)
  have hx_ge : 3 ≤ x := by
    have : x = 3 ∨ x = 4 ∨ x = 6 ∨ x = 10 ∨ x = 15 := by simpa using hxmem
    omega
  have hxz : x ≤ z := le_trans hxy hyz
  have h3x : 3 * x ≤ 7 := by
    calc
      3 * x = x + x + x := by ring
      _ ≤ x + y + z := by gcongr
      _ = 7 := hsum
  have : 9 ≤ 7 := by
    calc
      9 = 3 * 3 := by norm_num
      _ ≤ 3 * x := by gcongr
      _ ≤ 7 := h3x
  exact (by decide : ¬9 ≤ 7) this
