import Submission.PaleyData
open SimpleGraph Set
open scoped BigOperators
namespace Erdos595Paley
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option profiler true
private theorem triangle_sum (f : Fin 17 → Fin 17 → ℝ) :
    (∑ t : Fin 68, f (triangles t).1 (triangles t).2.1 +
      f (triangles t).1 (triangles t).2.2 + f (triangles t).2.1 (triangles t).2.2) =
      3 * ∑ e : Fin 68, f (edges e).1 (edges e).2 := by
  simp only [Fin.sum_univ_succ, triangles, edges, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  ring


#print axioms triangle_sum
end Erdos595Paley
