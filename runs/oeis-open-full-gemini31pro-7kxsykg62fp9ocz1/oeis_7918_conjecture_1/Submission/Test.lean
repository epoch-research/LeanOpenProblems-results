import Mathlib

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

-- wait, can we compute real powers using #eval? No.
-- But wait!
-- `(n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ)))`
-- If `1 / (n : ℝ)` is `1 / 8`, since both are Reals, it is `0.125`.
