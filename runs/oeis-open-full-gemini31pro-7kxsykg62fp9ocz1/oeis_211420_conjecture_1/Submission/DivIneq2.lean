import Mathlib

open Nat

lemma div_ineq_mod (u v M : ℕ) (hu : u < M) (hv : v < M) :
    (4 * u - v) / M + (3 * u) / M + (2 * u) / M ≤ (8 * u - 2 * v) / M + (8 * v) / M + u / M := by
  -- Since u < M, u / M = 0.
  -- 3*u / M \le 2, 2*u / M \le 1, etc.
  -- This is a finite problem, but M is symbolic!
  sorry
