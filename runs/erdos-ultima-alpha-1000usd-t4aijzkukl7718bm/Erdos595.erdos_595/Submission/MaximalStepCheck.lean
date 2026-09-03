import Submission.Work
#check WithTop.coe_natCast
#check WithTop.natCast_strictMono
#check WithTop.coe_natCast
example (n k : ℕ) : ((n+1:ℕ) : WithTop ℕ) ≤ (k:WithTop ℕ) ↔
    (n:WithTop ℕ) ≤ k ∧ ¬(k:WithTop ℕ) = n := by
  simp only [← WithTop.coe_natCast, Nat.cast_id, WithTop.coe_le_coe,WithTop.coe_inj]
  omega
