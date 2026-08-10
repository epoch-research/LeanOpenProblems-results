import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real
set_option linter.unusedSimpArgs false

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

example : b 2 = -(3/2) := by
  rw [b]
  rw [show (Icc 1 2 : Finset ℕ) = {1,2} by decide]
  simp [om1, om2]
  norm_num

#print axioms _example
