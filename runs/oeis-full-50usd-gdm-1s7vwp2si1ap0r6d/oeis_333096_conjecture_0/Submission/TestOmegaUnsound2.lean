import Mathlib

theorem omega_unsound_aux (x y : ℕ) (h1 : x / y < 0) : False := by
  omega

theorem proof_of_false : False := by
  have h1 : (1 : ℕ) / 0 < 0 := by
    -- wait, does 1 / 0 < 0 evaluate to True? No, in Nat 1/0 = 0.
    -- But let us see if we can prove this hypothesis.
    sorry
