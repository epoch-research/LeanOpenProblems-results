import FormalConjectures.Util.ProblemImports

open Polynomial Finset

lemma continuous_eval (p : ℝ[X]) : Continuous fun x => p.eval x := by
  simp only [eval_eq_sum]
  exact continuous_finset_sum _ fun c _ => continuous_const.mul (continuous_pow _)




