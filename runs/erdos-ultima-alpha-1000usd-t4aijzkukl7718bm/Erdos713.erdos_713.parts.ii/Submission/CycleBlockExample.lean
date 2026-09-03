import FormalConjecturesUtil
import Submission.CycleBlockAssembly

/-! A nineteen-vertex gluing of two ten-cycles with attained rate 6/5. -/
open SimpleGraph
namespace Erdos713CycleBlockExample
open Erdos713Gluing Erdos713Rate Erdos713RootPower Erdos713C10

def paired := wedge C10 (0 : Fin 10) C10 (1 : Fin 10)

lemma c10_no_isolates (x : Fin 10) : ∃ y, C10.Adj x y := by
  refine ⟨x+1,?_⟩
  rw [cycleGraph_adj]
  exact Or.inr (by simp)

lemma paired_rate : HasRate paired ((6 : ℝ)/5) := by
  simpa only [max_self] using wedge_rate C10 (0 : Fin 10) c10_no_isolates
    C10 (1 : Fin 10) (c10_no_isolates _) Erdos713C10.rate Erdos713C10.rate (c10 _)

lemma paired_assembly : Erdos713CycleAssembly.Assembly paired := by
  apply Erdos713CycleAssembly.Assembly.wedgeRooted C10 (0 : Fin 10) c10_no_isolates
    (6/5) (by simpa using Erdos713C10.rate) (by simpa using c10 (0 : Fin 10))
    C10 (1 : Fin 10) (c10_no_isolates _)
  exact .ten C10 (.refl _) (.refl _)

lemma paired_card : Fintype.card (Erdos713Gluing.Vertex (0 : Fin 10) (1 : Fin 10)) = 19 := by
  decide

#print axioms paired_rate
#print axioms paired_assembly
end Erdos713CycleBlockExample
