import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
noncomputable def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

lemma om1 : omega_mult 1 = 0 := by simp [omega_mult]
lemma om2 : omega_mult 2 = 1 := by
  unfold omega_mult
  rw [(by norm_num : Nat.Prime 2).factorization]
  simp

example : b 1 = -1 := by
  norm_num [b, om1]
example : b 2 = -3/2 := by
  norm_num [b, om1, om2]
example : b 2 < -1 / sqrt (2 : ℝ) := by
  have hb : b 2 = -3/2 := by norm_num [b, om1, om2]
  rw [hb]
  have hs : Real.sqrt (2:ℝ) < 2 := by nlinarith [Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num), Real.sqrt_nonneg (2:ℝ)]
  have hpos : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos_of_pos (by norm_num)
  -- -3/2 < -1/sqrt2 iff 1/sqrt2 < 3/2
  rw [neg_div]
  nlinarith [one_div_pos.mpr hpos, inv_lt_of_inv_lt₀ (by norm_num : (0:ℝ) < (3/2)) hpos]
