import Mathlib

def get_valid_pair (d : ℕ) : ℕ × ℕ :=
  let pairs := [(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (3, 5), (3, 7), (3, 11), (3, 17), (5, 7), (5, 11), (5, 13), (7, 11), (7, 13), (11, 13)]
  pairs.find? (fun ⟨p, q⟩ => d % p ≠ 0 ∧ d % q ≠ 0) |>.getD (2, 3)

def d_is_bad (d : ℕ) : Bool :=
  let ⟨p, q⟩ := get_valid_pair d
  p.minFac == p && q.minFac == q

theorem all_d_primes : ((List.range 2026).drop 1).all d_is_bad = true := by decide
