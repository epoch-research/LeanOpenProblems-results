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
  simp [b, om1]

example : b 2 = -3/2 := by
  simp [b, om1, om2]
  norm_num

example : b 2 < -1 / sqrt (2 : ℝ) := by
  rw [show b 2 = -3/2 by
    simp [b, om1, om2]
    norm_num]
  have hs : sqrt (2:ℝ) < 2 := by nlinarith [sq_sqrt (by norm_num : (0:ℝ) ≤ 2), sqrt_nonneg (2:ℝ)]
  have hp : 0 < sqrt (2:ℝ) := sqrt_pos.2 (by norm_num)
  nlinarith
