import Mathlib

open Nat

def a (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) fun n =>
    Finset.sum (Finset.range (n + 1)) fun k =>
      let exp_x_num := n * (k + 1)
      if exp_x_num ≤ m then
        let remainder := m - exp_x_num
        if (n + 1) ∣ remainder then
          let j : ℕ := remainder / (n + 1)
          let c₁ : ℤ := (n.choose k)
          let c₂ : ℤ := (choose (n + j) j)
          let sign : ℤ := if Even j then 1 else -1
          sign * c₁ * c₂
        else
          0
      else
        0

theorem oeis_323557_conjecture_0 (m : ℕ) : Odd (a m) → ∃ n : ℕ, m = n * (n + 1) := by
  sorry
