import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Icc 1 n) fun k : ℕ =>
    (k : ℚ) ^ (moebius k : ℤ)
  ).den

theorem a2 : a 2 = primorial 2 := by
  unfold a
  unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := by
    exact moebius_apply_prime (by decide)
  rw [h2]
  norm_num
  decide

theorem a3 : a 3 = primorial 3 := by
  unfold a
  unfold primorial
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  rw [sum_Icc_succ_top (by decide)]
  simp
  have h2 : moebius 2 = -1 := by
    exact moebius_apply_prime (by decide)
  have h3 : moebius 3 = -1 := by
    exact moebius_apply_prime (by decide)
  rw [h2, h3]
  norm_num
  decide


#print axioms a2
