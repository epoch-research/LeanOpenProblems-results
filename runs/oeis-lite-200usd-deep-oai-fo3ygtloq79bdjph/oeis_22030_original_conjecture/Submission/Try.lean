import FormalConjectures.Util.ProblemImports

lemma ceil_pred_div {q d r : ℕ} (hd : 0 < d) (hr0 : 0 < r) (hrle : r ≤ d) :
    ((q * d + r + d - 1) / d - 1 = q) := by
  have hle' : q * d + d ≤ q * d + r + d - 1 := by omega
  have hle : (q + 1) * d ≤ q * d + r + d - 1 := by
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle'
  have hlt' : q * d + r + d - 1 < q * d + (d + d) := by omega
  have hlt : q * d + r + d - 1 < (q + 2) * d := by
    simpa [Nat.add_mul, Nat.succ_mul, Nat.one_mul, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt'
  have hdiv : (q * d + r + d - 1) / d = q + 1 := Nat.div_eq_of_lt_le hle hlt
  omega
