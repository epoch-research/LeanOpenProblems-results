import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X - C (1/2 : ℝ))^(2 * m)

lemma eval_P_map (m : ℕ) (z : ℂ) :
    ((P_witness_gen m).map (algebraMap ℝ ℂ)).eval z = (z - 1/2)^(2 * m) := by
  unfold P_witness_gen
  simp

theorem roots_P (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (h : ((P_witness_gen m).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc 0 1 := by
  have h_eval := eval_P_map m z
  rw [h] at h_eval
  have h_z : z - 1/2 = 0 := eq_zero_of_pow_eq_zero h_eval.symm
  have h_eq : z = 1/2 := by linarith
  subst h_eq
  simp
  constructor <;> norm_num
