import FormalConjectures.Util.ProblemImports

open Complex

lemma nz (n : ℕ) (hn_gt_one : 1 < n) : riemannZeta (n : ℂ) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simp only [natCast_re]
  exact_mod_cast hn_gt_one








