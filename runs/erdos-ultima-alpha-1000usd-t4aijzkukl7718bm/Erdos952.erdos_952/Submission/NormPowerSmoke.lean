import Submission.NormEightRuns
#check Zsqrtd.normMonoidHom
#check MonoidHom.map_pow
#check IsCoprime.pow_left
#check Zsqrtd.norm_eq_mul_conj
#check Int.even_iff
#check Even
example (z : GaussianInt) (k : ℕ) : (z^k).norm = z.norm^k := by
  exact (Zsqrtd.normMonoidHom.map_pow z k)
example (k : ℕ) : IsCoprime ((2 : ℤ)^k) 65 := by
  exact (show IsCoprime (2 : ℤ) 65 from ⟨-32,1,by norm_num⟩).pow_left
