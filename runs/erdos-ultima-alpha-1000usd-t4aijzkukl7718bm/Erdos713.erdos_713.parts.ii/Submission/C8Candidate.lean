import FormalConjecturesUtil
import Submission.UpToCubicNorm

/-! An explicit obstruction to a proposed four-coordinate incidence construction.
This candidate does contain an eight-cycle, so it cannot close the C8 lower-bound gap. -/

open SimpleGraph
namespace Erdos713C8Candidate

def Rel (p l : ℚ × (Fin 3 → ℚ)) : Prop :=
  p.2 0 = l.1*p.1 + l.2 0 ∧
  p.2 1 = l.1^2*p.1 + l.2 1 ∧
  p.2 2 = l.1*p.1^2 + l.2 2

abbrev graph := Erdos713C6.bipGraph Rel

def chain : Fin 8 → (ℚ × (Fin 3 → ℚ)) ⊕ (ℚ × (Fin 3 → ℚ)) :=
  ![Sum.inl (0, ![0,0,0]), Sum.inr (0, ![0,0,0]),
    Sum.inl (-1, ![0,0,0]), Sum.inr (1, ![1,1,-1]),
    Sum.inl (2, ![3,3,3]), Sum.inr (3, ![-3,-15,-9]),
    Sum.inl (3, ![6,12,18]), Sum.inr (2, ![0,0,0])]

set_option maxHeartbeats 1000000 in
lemma contains_octagon : cycleGraph 8 ⊑ graph := by
  refine ⟨⟨⟨chain, ?_⟩, ?_⟩⟩
  · intro i j
    simp only [cycleGraph_adj, graph, Erdos713C6.bipGraph, Rel]
    fin_cases i <;> fin_cases j <;> dsimp [chain] <;> norm_num <;> decide
  · change Function.Injective chain
    unfold Function.Injective chain
    decide

#print axioms contains_octagon
end Erdos713C8Candidate
