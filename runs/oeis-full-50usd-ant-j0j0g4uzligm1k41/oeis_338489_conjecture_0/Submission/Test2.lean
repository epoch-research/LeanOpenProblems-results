import FormalConjectures.Util.ProblemImports
open Nat Int

def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

theorem test :
    ∀ n : ℕ, is_triangular n.factorial ↔ n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5 := by
  intro n
  constructor
  · intro h
    -- forward direction
    rcases n with _|_|_|_|_|_|m
    · tauto
    · tauto
    · -- n = 2 : is_triangular 2 is false
      exfalso; obtain ⟨k, hk⟩ := h
      rw [show Nat.factorial 2 = 2 from rfl] at hk
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · interval_cases k <;> omega
      · have : 3 ≤ k*(k+1)/2 := by
          calc 3 = 2*(2+1)/2 := by norm_num
            _ ≤ k*(k+1)/2 := Nat.div_le_div_right (Nat.mul_le_mul hge (by omega))
        omega
    · tauto
    · -- n = 4 : is_triangular 24 is false
      exfalso; obtain ⟨k, hk⟩ := h
      rw [show Nat.factorial 4 = 24 from rfl] at hk
      rcases Nat.lt_or_ge k 7 with hlt | hge
      · interval_cases k <;> omega
      · have : 28 ≤ k*(k+1)/2 := by
          calc 28 = 7*(7+1)/2 := by norm_num
            _ ≤ k*(k+1)/2 := Nat.div_le_div_right (Nat.mul_le_mul hge (by omega))
        omega
    · tauto
    · -- n = m + 6 : the open Brocard-type core
      sorry
  · intro h
    rcases h with h|h|h|h <;> subst h
    · exact ⟨1, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨15, by decide⟩
