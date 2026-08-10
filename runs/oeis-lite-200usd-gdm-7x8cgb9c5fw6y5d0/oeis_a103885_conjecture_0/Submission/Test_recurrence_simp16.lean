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
