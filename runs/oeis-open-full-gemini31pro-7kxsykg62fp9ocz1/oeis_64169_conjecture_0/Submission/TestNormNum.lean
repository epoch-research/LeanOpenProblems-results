import FormalConjectures.Util.ProblemImports
open Rat
set_option maxRecDepth 1000000

lemma H_1000 : (harmonic 1000).num > 0 := by
  unfold harmonic
  repeat rw [Finset.sum_range_succ]
  rw [Finset.sum_range_zero]
  norm_num
