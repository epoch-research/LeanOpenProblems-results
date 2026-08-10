import FormalConjectures.Util.ProblemImports
open Nat Int

def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

-- helper: for bounded x, decide by bounding k
example : ¬ is_triangular (Nat.factorial 2) := by
  rintro ⟨k, hk⟩
  rw [show Nat.factorial 2 = 2 from rfl] at hk
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> omega
  · have : 3 ≤ k*(k+1)/2 := by
      calc 3 = 2*(2+1)/2 := by norm_num
        _ ≤ k*(k+1)/2 := Nat.div_le_div_right (Nat.mul_le_mul h (by omega))
    omega
example : ¬ is_triangular (Nat.factorial 4) := by
  rintro ⟨k, hk⟩
  rw [show Nat.factorial 4 = 24 from rfl] at hk
  rcases Nat.lt_or_ge k 7 with h | h
  · interval_cases k <;> omega
  · have : 28 ≤ k*(k+1)/2 := by
      calc 28 = 7*(7+1)/2 := by norm_num
        _ ≤ k*(k+1)/2 := Nat.div_le_div_right (Nat.mul_le_mul h (by omega))
    omega
