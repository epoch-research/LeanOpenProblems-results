import FormalConjectures.Util.ProblemImports

example {N j : ℕ} (hlo : 2^(j+1) ≤ N) (hhi : N < 3*2^j) : N / 2^j = 2 := by
  have hp : 0 < 2^j := pow_pos (by norm_num) _
  have hlo' : 2 ≤ N / 2^j := by
    rw [Nat.le_div_iff_mul_le hp]
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlo
  have hhi' : N / 2^j < 3 := by
    rw [Nat.div_lt_iff_lt_mul hp]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi
  omega
