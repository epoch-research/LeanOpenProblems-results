import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

-- Bertrand gives a prime below n^3, but only above n^3/2.
example (n : ℕ) (hn : 0 < n) : ∃ p, Nat.Prime p ∧ n^3 / 2 < p ∧ p ≤ n^3 := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n^3 / 2) (by
    intro h
    have : n^3 < 2 := by omega
    nlinarith [hn]
  )
  refine ⟨p,hp,hlo,?_⟩
  have h : 2 * (n^3 / 2) ≤ n^3 := Nat.mul_div_le _ _
  exact hhi.trans h

-- But the missing inequality is false for large n.
example : ¬ (∀ n : ℕ, 14 ≤ n → n^3 - n ≤ n^3 / 2) := by
  intro h
  have := h 14 (by norm_num)
  norm_num at this
