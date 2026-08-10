import FormalConjectures.Util.ProblemImports
#check Nat.exists_mul_self
#check Nat.exists_mul_self'
#check Nat.sqrt_eq'
#check Nat.sqrt_le'
#check Nat.lt_succ_sqrt'
example (m : ℕ) : (m.sqrt ^ 2 = m) ↔ ∃ q, q^2 = m := by
  rw [← Nat.exists_mul_self']
  constructor <;> intro h
  · exact ⟨m.sqrt, h⟩
  · simpa using h
example (m : ℕ) : m.sqrt ^ 2 = m := by
  simp?
