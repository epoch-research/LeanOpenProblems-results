import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def check_pair (p q d : ℕ) : Bool :=
  let pq := p * q
  (List.range pq).all (fun a =>
    (List.range pq).any (fun i => (a + i * d) % p == 0 && (a + i * d) % q == 0)
  )

def get_valid_pair (d : ℕ) : ℕ × ℕ :=
  let pairs := [(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (3, 5), (3, 7), (3, 11), (3, 17), (5, 7), (5, 11), (5, 13), (7, 11), (7, 13), (11, 13)]
  pairs.find? (fun ⟨p, q⟩ => d % p ≠ 0 ∧ d % q ≠ 0) |>.getD (2, 3)

def d_is_bad (d : ℕ) : Bool :=
  let ⟨p, q⟩ := get_valid_pair d
  p * q ≤ 150 && p % 10 ≠ q % 10 && check_pair p q d

theorem all_d_bad : ((List.range 2026).drop 1).all d_is_bad = true := by decide
