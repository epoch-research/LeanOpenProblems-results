import Submission.ContractionContractedData

/-! Cached finite data for an auxiliary contraction obstruction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGap
open Critical Rigidity BlockRestriction CycleCertificates
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

def f0 : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 8 by decide +kernel) (.cons (show graph.Adj 8 14 by decide +kernel) (.cons (show graph.Adj 14 10 by decide +kernel) (.cons (show graph.Adj 10 6 by decide +kernel) (.cons (show graph.Adj 6 13 by decide +kernel) (.cons (show graph.Adj 13 7 by decide +kernel) (.cons (show graph.Adj 7 3 by decide +kernel) (.cons (show graph.Adj 3 12 by decide +kernel) (.cons (show graph.Adj 12 2 by decide +kernel) (.cons (show graph.Adj 2 4 by decide +kernel) (.cons (show graph.Adj 4 9 by decide +kernel) (.cons (show graph.Adj 9 11 by decide +kernel) (.cons (show graph.Adj 11 5 by decide +kernel) (.cons (show graph.Adj 5 1 by decide +kernel) (.cons (show graph.Adj 1 22 by decide +kernel) (.cons (show graph.Adj 22 28 by decide +kernel) (.cons (show graph.Adj 28 24 by decide +kernel) (.cons (show graph.Adj 24 20 by decide +kernel) (.cons (show graph.Adj 20 27 by decide +kernel) (.cons (show graph.Adj 27 21 by decide +kernel) (.cons (show graph.Adj 21 17 by decide +kernel) (.cons (show graph.Adj 17 26 by decide +kernel) (.cons (show graph.Adj 26 16 by decide +kernel) (.cons (show graph.Adj 16 18 by decide +kernel) (.cons (show graph.Adj 18 23 by decide +kernel) (.cons (show graph.Adj 23 25 by decide +kernel) (.cons (show graph.Adj 25 19 by decide +kernel) (.cons (show graph.Adj 19 15 by decide +kernel) (.cons (show graph.Adj 15 0 by decide +kernel) .nil)))))))))))))))))))))))))))))

lemma f0_cycle : f0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def f1 : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 9 by decide +kernel) (.cons (show graph.Adj 9 7 by decide +kernel) (.cons (show graph.Adj 7 3 by decide +kernel) (.cons (show graph.Adj 3 12 by decide +kernel) (.cons (show graph.Adj 12 2 by decide +kernel) (.cons (show graph.Adj 2 4 by decide +kernel) (.cons (show graph.Adj 4 14 by decide +kernel) (.cons (show graph.Adj 14 8 by decide +kernel) (.cons (show graph.Adj 8 10 by decide +kernel) (.cons (show graph.Adj 10 13 by decide +kernel) (.cons (show graph.Adj 13 6 by decide +kernel) (.cons (show graph.Adj 6 11 by decide +kernel) (.cons (show graph.Adj 11 5 by decide +kernel) (.cons (show graph.Adj 5 1 by decide +kernel) (.cons (show graph.Adj 1 23 by decide +kernel) (.cons (show graph.Adj 23 21 by decide +kernel) (.cons (show graph.Adj 21 17 by decide +kernel) (.cons (show graph.Adj 17 26 by decide +kernel) (.cons (show graph.Adj 26 16 by decide +kernel) (.cons (show graph.Adj 16 18 by decide +kernel) (.cons (show graph.Adj 18 28 by decide +kernel) (.cons (show graph.Adj 28 22 by decide +kernel) (.cons (show graph.Adj 22 24 by decide +kernel) (.cons (show graph.Adj 24 27 by decide +kernel) (.cons (show graph.Adj 27 20 by decide +kernel) (.cons (show graph.Adj 20 25 by decide +kernel) (.cons (show graph.Adj 25 19 by decide +kernel) (.cons (show graph.Adj 19 15 by decide +kernel) (.cons (show graph.Adj 15 0 by decide +kernel) .nil)))))))))))))))))))))))))))))

lemma f1_cycle : f1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def f2 : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 7 by decide +kernel) (.cons (show graph.Adj 7 9 by decide +kernel) (.cons (show graph.Adj 9 11 by decide +kernel) (.cons (show graph.Adj 11 4 by decide +kernel) (.cons (show graph.Adj 4 14 by decide +kernel) (.cons (show graph.Adj 14 2 by decide +kernel) (.cons (show graph.Adj 2 3 by decide +kernel) (.cons (show graph.Adj 3 13 by decide +kernel) (.cons (show graph.Adj 13 10 by decide +kernel) (.cons (show graph.Adj 10 6 by decide +kernel) (.cons (show graph.Adj 6 5 by decide +kernel) (.cons (show graph.Adj 5 12 by decide +kernel) (.cons (show graph.Adj 12 1 by decide +kernel) (.cons (show graph.Adj 1 8 by decide +kernel) (.cons (show graph.Adj 8 0 by decide +kernel) .nil)))))))))))))))

lemma f2_cycle : f2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def f3 : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 7 by decide +kernel) (.cons (show graph.Adj 7 13 by decide +kernel) (.cons (show graph.Adj 13 3 by decide +kernel) (.cons (show graph.Adj 3 2 by decide +kernel) (.cons (show graph.Adj 2 14 by decide +kernel) (.cons (show graph.Adj 14 10 by decide +kernel) (.cons (show graph.Adj 10 8 by decide +kernel) (.cons (show graph.Adj 8 1 by decide +kernel) (.cons (show graph.Adj 1 12 by decide +kernel) (.cons (show graph.Adj 12 5 by decide +kernel) (.cons (show graph.Adj 5 6 by decide +kernel) (.cons (show graph.Adj 6 11 by decide +kernel) (.cons (show graph.Adj 11 4 by decide +kernel) (.cons (show graph.Adj 4 9 by decide +kernel) (.cons (show graph.Adj 9 0 by decide +kernel) .nil)))))))))))))))

lemma f3_cycle : f3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def f4 : graph.Walk 1 1 :=
  (.cons (show graph.Adj 1 21 by decide +kernel) (.cons (show graph.Adj 21 23 by decide +kernel) (.cons (show graph.Adj 23 25 by decide +kernel) (.cons (show graph.Adj 25 18 by decide +kernel) (.cons (show graph.Adj 18 28 by decide +kernel) (.cons (show graph.Adj 28 16 by decide +kernel) (.cons (show graph.Adj 16 17 by decide +kernel) (.cons (show graph.Adj 17 27 by decide +kernel) (.cons (show graph.Adj 27 24 by decide +kernel) (.cons (show graph.Adj 24 20 by decide +kernel) (.cons (show graph.Adj 20 19 by decide +kernel) (.cons (show graph.Adj 19 26 by decide +kernel) (.cons (show graph.Adj 26 15 by decide +kernel) (.cons (show graph.Adj 15 22 by decide +kernel) (.cons (show graph.Adj 22 1 by decide +kernel) .nil)))))))))))))))

lemma f4_cycle : f4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def f5 : graph.Walk 1 1 :=
  (.cons (show graph.Adj 1 21 by decide +kernel) (.cons (show graph.Adj 21 27 by decide +kernel) (.cons (show graph.Adj 27 17 by decide +kernel) (.cons (show graph.Adj 17 16 by decide +kernel) (.cons (show graph.Adj 16 28 by decide +kernel) (.cons (show graph.Adj 28 24 by decide +kernel) (.cons (show graph.Adj 24 22 by decide +kernel) (.cons (show graph.Adj 22 15 by decide +kernel) (.cons (show graph.Adj 15 26 by decide +kernel) (.cons (show graph.Adj 26 19 by decide +kernel) (.cons (show graph.Adj 19 20 by decide +kernel) (.cons (show graph.Adj 20 25 by decide +kernel) (.cons (show graph.Adj 25 18 by decide +kernel) (.cons (show graph.Adj 18 23 by decide +kernel) (.cons (show graph.Adj 23 1 by decide +kernel) .nil)))))))))))))))

lemma f5_cycle : f5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def froot : Fin 6 → Fin 29 := ![0,0,0,0,1,1]
def fwalk : ∀ i : Fin 6, graph.Walk (froot i) (froot i)
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | 3 => f3
  | 4 => f4
  | 5 => f5

lemma fwalk_cycle (i : Fin 6) : (fwalk i).IsCycle := by
  fin_cases i
  · exact f0_cycle
  · exact f1_cycle
  · exact f2_cycle
  · exact f3_cycle
  · exact f4_cycle
  · exact f5_cycle

lemma fractional_cover_twice : ∀ x y : Fin 29,
    (Finset.univ.filter (fun i : Fin 6 => s(x,y) ∈ (fwalk i).edges)).card =
      if graph.Adj x y then 2 else 0 := by
  intro x
  fin_cases x <;> decide +kernel

lemma fractional_cover (e : Sym2 (Fin 29)) :
    (∑ i : Fin 6, if e ∈ (fwalk i).toSubgraph.edgeSet then (1/2 : ℝ) else 0) =
      if e ∈ graph.edgeSet then 1 else 0 := by
  simp only [Walk.mem_edges_toSubgraph,Finset.sum_ite,Finset.sum_const_zero,add_zero,
    Finset.sum_const]
  induction e using Sym2.ind with | _ x y =>
    rw [fractional_cover_twice]
    by_cases h : graph.Adj x y <;> simp [h]

lemma fractional_cost : (∑ _i : Fin 6, (1/2 : ℝ)) = 3 := by norm_num


end Erdos184Work.ContractionGap
