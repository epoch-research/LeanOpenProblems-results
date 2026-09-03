import Submission.ContractionBaseData

/-! Cached finite data for an auxiliary contraction obstruction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGap
open Critical Rigidity BlockRestriction CycleCertificates
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

def q0 : contracted.Walk 0 0 :=
  (.cons (show contracted.Adj 0 7 by decide +kernel) (.cons (show contracted.Adj 7 3 by decide +kernel) (.cons (show contracted.Adj 3 2 by decide +kernel) (.cons (show contracted.Adj 2 4 by decide +kernel) (.cons (show contracted.Adj 4 9 by decide +kernel) (.cons (show contracted.Adj 9 11 by decide +kernel) (.cons (show contracted.Adj 11 5 by decide +kernel) (.cons (show contracted.Adj 5 1 by decide +kernel) (.cons (show contracted.Adj 1 21 by decide +kernel) (.cons (show contracted.Adj 21 17 by decide +kernel) (.cons (show contracted.Adj 17 16 by decide +kernel) (.cons (show contracted.Adj 16 18 by decide +kernel) (.cons (show contracted.Adj 18 23 by decide +kernel) (.cons (show contracted.Adj 23 25 by decide +kernel) (.cons (show contracted.Adj 25 19 by decide +kernel) (.cons (show contracted.Adj 19 0 by decide +kernel) .nil))))))))))))))))

lemma q0_cycle : q0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def q1 : contracted.Walk 0 0 :=
  (.cons (show contracted.Adj 0 8 by decide +kernel) (.cons (show contracted.Adj 8 10 by decide +kernel) (.cons (show contracted.Adj 10 13 by decide +kernel) (.cons (show contracted.Adj 13 6 by decide +kernel) (.cons (show contracted.Adj 6 11 by decide +kernel) (.cons (show contracted.Adj 11 4 by decide +kernel) (.cons (show contracted.Adj 4 14 by decide +kernel) (.cons (show contracted.Adj 14 2 by decide +kernel) (.cons (show contracted.Adj 2 12 by decide +kernel) (.cons (show contracted.Adj 12 1 by decide +kernel) (.cons (show contracted.Adj 1 22 by decide +kernel) (.cons (show contracted.Adj 22 24 by decide +kernel) (.cons (show contracted.Adj 24 27 by decide +kernel) (.cons (show contracted.Adj 27 20 by decide +kernel) (.cons (show contracted.Adj 20 25 by decide +kernel) (.cons (show contracted.Adj 25 18 by decide +kernel) (.cons (show contracted.Adj 18 28 by decide +kernel) (.cons (show contracted.Adj 28 16 by decide +kernel) (.cons (show contracted.Adj 16 26 by decide +kernel) (.cons (show contracted.Adj 26 0 by decide +kernel) .nil))))))))))))))))))))

lemma q1_cycle : q1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def q2 : contracted.Walk 0 0 :=
  (.cons (show contracted.Adj 0 9 by decide +kernel) (.cons (show contracted.Adj 9 7 by decide +kernel) (.cons (show contracted.Adj 7 13 by decide +kernel) (.cons (show contracted.Adj 13 3 by decide +kernel) (.cons (show contracted.Adj 3 12 by decide +kernel) (.cons (show contracted.Adj 12 5 by decide +kernel) (.cons (show contracted.Adj 5 6 by decide +kernel) (.cons (show contracted.Adj 6 10 by decide +kernel) (.cons (show contracted.Adj 10 14 by decide +kernel) (.cons (show contracted.Adj 14 8 by decide +kernel) (.cons (show contracted.Adj 8 1 by decide +kernel) (.cons (show contracted.Adj 1 23 by decide +kernel) (.cons (show contracted.Adj 23 21 by decide +kernel) (.cons (show contracted.Adj 21 27 by decide +kernel) (.cons (show contracted.Adj 27 17 by decide +kernel) (.cons (show contracted.Adj 17 26 by decide +kernel) (.cons (show contracted.Adj 26 19 by decide +kernel) (.cons (show contracted.Adj 19 20 by decide +kernel) (.cons (show contracted.Adj 20 24 by decide +kernel) (.cons (show contracted.Adj 24 28 by decide +kernel) (.cons (show contracted.Adj 28 22 by decide +kernel) (.cons (show contracted.Adj 22 0 by decide +kernel) .nil))))))))))))))))))))))

lemma q2_cycle : q2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def qroot : Fin 3 → Fin 29 := ![0,0,0]
def qwalk : ∀ i : Fin 3, contracted.Walk (qroot i) (qroot i)
  | 0 => q0
  | 1 => q1
  | 2 => q2

lemma qwalk_cycle (i : Fin 3) : (qwalk i).IsCycle := by
  fin_cases i
  · exact q0_cycle
  · exact q1_cycle
  · exact q2_cycle

lemma qwalk_disjoint : ∀ i j : Fin 3, i ≠ j →
    Disjoint (qwalk i).edges.toFinset (qwalk j).edges.toFinset := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | skip
  all_goals
    simp only [qwalk,q0,q1,q2,
      Walk.edges_cons,Walk.edges_nil,List.disjoint_toFinset_iff_disjoint,List.disjoint_iff_ne,
      List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    repeat' apply And.intro
    all_goals decide +kernel

lemma qwalk_cover : ∀ x y : Fin 29, contracted.Adj x y ↔
    ∃ i : Fin 3, s(x,y) ∈ (qwalk i).edges.toFinset := by
  simp only [List.mem_toFinset]
  decide +kernel

lemma contracted_upper : number contracted ≤ 3 := by
  have h := DiminishingReturns.number_le_cycle_family qroot qwalk qwalk_cycle
    (by simpa only [List.disjoint_toFinset_iff_disjoint] using qwalk_disjoint)
    (by simpa only [List.mem_toFinset] using qwalk_cover)
  simpa only [Fintype.card_fin] using h

lemma contracted_number : number contracted = 3 := by
  have hlo := StarCore.number_degree_bound contracted 0
  have hd := contracted_degree_zero
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hlo hd
  have hhi := contracted_upper
  omega

end Erdos184Work.ContractionGap
