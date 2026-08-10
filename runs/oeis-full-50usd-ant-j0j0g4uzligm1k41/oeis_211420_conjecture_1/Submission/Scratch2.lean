import Mathlib
open Finset
set_option maxHeartbeats 1000000

axiom keyfloor_int (q n r : ℤ) (hq : 0 < q) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    (2*n)/q + (3*n)/q + (4*n - r)/q ≤ (8*r)/q + n/q + (8*n - 2*r)/q

theorem keyfloor_nat (q n r : ℕ) (hq : 0 < q) (hr : r ≤ 4*n) :
    2*n/q + 3*n/q + (4*n-r)/q ≤ 8*r/q + n/q + (8*n-2*r)/q := by
  have h2r : 2*r ≤ 8*n := by omega
  rw [← Nat.cast_le (α := ℤ)]
  push_cast [Int.natCast_ediv, Nat.cast_sub hr, Nat.cast_sub h2r]
  have := keyfloor_int q n r (by exact_mod_cast hq) (by positivity) (by positivity)
  convert this using 2 <;> ring
