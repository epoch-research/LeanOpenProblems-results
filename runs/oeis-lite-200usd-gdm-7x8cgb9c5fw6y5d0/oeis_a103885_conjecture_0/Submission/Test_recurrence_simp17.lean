import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def Q_witness_gen (m : ℕ) : Polynomial ℝ := X^(2 * m)

lemma eval_Q_map (m : ℕ) (z : ℂ) :
    ((Q_witness_gen m).map (algebraMap ℝ ℂ)).eval (z^2) = z^(4 * m) := by
  unfold Q_witness_gen
  simp
  rw [← pow_mul]
  congr 1
  ring

theorem roots_Q (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (h : ((Q_witness_gen m).map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1) 1 := by
  have h_eval := eval_Q_map m z
  rw [h] at h_eval
  have h_z : z = 0 := eq_zero_of_pow_eq_zero h_eval.symm
  subst h_z
  simp
  constructor <;> norm_num
