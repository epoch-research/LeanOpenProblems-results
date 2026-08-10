import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial

noncomputable def P_witness_gen (m : ℕ) : Polynomial ℝ := (X - C (1/2 : ℝ))^(2 * m)

lemma eval_P_map (m : ℕ) (z : ℂ) :
    ((P_witness_gen m).map (algebraMap ℝ ℂ)).eval z = (z - 1/2)^(2 * m) := by
  unfold P_witness_gen
  simp
