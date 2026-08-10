import FormalConjectures.Util.ProblemImports
open Nat

example (n : ℕ) (h : 1 ≤ n) : ∃ p, p.Prime ∧ n ^ 3 / 2 < p ∧ p ≤ n ^ 3 := by
  have hm : n ^ 3 / 2 ≠ 0 := by
    intro hz
    have : n = 1 ∨ 2 ≤ n := by omega
    rcases this with rfl | hn
    · norm_num at hz
    · have : 1 ≤ n ^ 3 / 2 := by
        have : 2 ≤ n ^ 3 := by nlinarith
        exact Nat.one_le_div_iff.mpr (by omega)
      omega
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n^3 / 2) hm
  refine ⟨p,hp,hlo,?_⟩
  calc p ≤ 2 * (n^3 / 2) := hhi
    _ ≤ n^3 := by omega
