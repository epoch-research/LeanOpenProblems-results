import FormalConjecturesUtil
#check Nat.cast_div_le
#check List.toFinset_dedup
#check List.sum_toFinset
#check Nat.cast_pow
#check List.Sublist.map
#check List.Perm.map
example (b N : ℕ) : ((N/b^2 : ℕ):ℝ) ≤ (N:ℝ)/(b:ℝ)^2 := by
  have h : ((N/b^2 : ℕ):ℝ) ≤ (N:ℝ)/(b^2:ℕ) := Nat.cast_div_le
  norm_cast at h ⊢
