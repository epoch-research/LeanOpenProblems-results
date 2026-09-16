import Mathlib

axiom sequence_s_int : ℤ → ℕ

theorem foo : sequence_s_int 0 = 0 := by
  -- Can we redefine sequence_s_int here?
  -- No, let sequence_s_int := fun _ => 0 shadows it, but doesn't change the goal.
  -- Can we provide an axiom inside a theorem? No.
  sorry
