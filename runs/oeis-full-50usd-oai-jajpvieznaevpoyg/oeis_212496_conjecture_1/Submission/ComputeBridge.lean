import FormalConjectures.Util.ProblemImports

open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
noncomputable def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

def bq (n : ℕ) : ℚ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℚ) / (k : ℚ)

lemma b_eq_bq (n : ℕ) : b n = (bq n : ℝ) := by
  unfold b bq
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]

example : bq 50 < 0 := by
  decide


#eval bq 2009
#eval ((bq 2009)^2 <= (1/2009 : ℚ))

example : b 2009 > -log (log (2009 : ℝ)) / sqrt (2009 : ℝ) := by
  rw [b_eq_bq]
  norm_num
  -- need log bounds
  sorry
