import Submission.PaleyData
open Erdos595Paley
open scoped BigOperators
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
set_option profiler true
example (f : Fin 17 → Fin 17 → ℝ) :
    (∑ j : Fin 17, (C 0 j : ℝ) * f (min 0 j) (max 0 j)) =
      3757 * f 0 0 + 1445 * (f 0 1 + f 0 2 + f 0 4 + f 0 8 + f 0 9 + f 0 13 + f 0 15 + f 0 16) := by
  simp only [Fin.sum_univ_succ, C, adjacent, min_def, max_def, Fin.ext_iff, Fin.le_def]
  norm_num
  ring!
