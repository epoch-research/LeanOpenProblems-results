import Mathlib

/- axiom sequence_s_int : ℤ → ℕ -/
def sequence_s_int : ℤ → ℕ := fun _ => 0

theorem foo : sequence_s_int 0 = 0 := rfl
