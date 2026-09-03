import Submission.PaleyData
open Erdos595Paley
open scoped BigOperators
#check fun (f : Fin 17 → Fin 17 → ℝ) =>
    (∑ t : Fin 68, f (triangles t).1 (triangles t).2.1 +
      f (triangles t).1 (triangles t).2.2 + f (triangles t).2.1 (triangles t).2.2)
#check fun (f : Fin 3 → ℝ) => ∑ t : Fin 3, f t + f t + f t
#check Fin.sum_univ_succ
#check List.sum_ofFn
