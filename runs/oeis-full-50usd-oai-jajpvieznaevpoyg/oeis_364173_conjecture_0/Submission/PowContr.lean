import FormalConjectures.Util.ProblemImports
example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) : p ^ r ≠ p ^ (r - 1) := by
  rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr) with ⟨s, rfl⟩
  simp only [Nat.succ_sub_one]
  intro h
  rw [pow_succ'] at h
  have h' : p * p ^ s = 1 * p ^ s := by simpa using h
  have hp1 : p = 1 := Nat.mul_right_cancel (pow_pos hp.pos s) h'
  omega
