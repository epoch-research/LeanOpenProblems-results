import Submission.TightDual

/-! A finite obstruction to contraction control of the integral--fractional gap.
This is auxiliary research, not a disproof of Erdős 184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGap
open Critical Rigidity BlockRestriction CycleCertificates
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

def edges : Finset (Sym2 (Fin 29)) :=
  {s(0,7), s(0,8), s(0,9), s(1,5), s(1,8), s(1,12), s(2,3), s(2,4), s(2,12), s(2,14), s(3,7), s(3,12), s(3,13), s(4,9), s(4,11), s(4,14), s(5,6), s(5,11), s(5,12), s(6,10), s(6,11), s(6,13), s(7,9), s(7,13), s(8,10), s(8,14), s(9,11), s(10,13), s(10,14), s(1,21), s(1,22), s(1,23), s(15,19), s(15,22), s(15,26), s(16,17), s(16,18), s(16,26), s(16,28), s(17,21), s(17,26), s(17,27), s(18,23), s(18,25), s(18,28), s(19,20), s(19,25), s(19,26), s(20,24), s(20,25), s(20,27), s(21,23), s(21,27), s(22,24), s(22,28), s(23,25), s(24,27), s(24,28), s(0,15)}

def edgeList : List (Fin 29 × Fin 29) :=
  [(0,7), (0,8), (0,9), (1,5), (1,8), (1,12), (2,3), (2,4), (2,12), (2,14), (3,7), (3,12), (3,13), (4,9), (4,11), (4,14), (5,6), (5,11), (5,12), (6,10), (6,11), (6,13), (7,9), (7,13), (8,10), (8,14), (9,11), (10,13), (10,14), (1,21), (1,22), (1,23), (15,19), (15,22), (15,26), (16,17), (16,18), (16,26), (16,28), (17,21), (17,26), (17,27), (18,23), (18,25), (18,28), (19,20), (19,25), (19,26), (20,24), (20,25), (20,27), (21,23), (21,27), (22,24), (22,28), (23,25), (24,27), (24,28), (0,15)]

def graph : SimpleGraph (Fin 29) := SimpleGraph.fromRel (fun x y => (x,y) ∈ edgeList)
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def contracted : SimpleGraph (Fin 29) := CertificateStructure.contract graph 0 15
instance : DecidableRel contracted.Adj := by unfold contracted CertificateStructure.contract; infer_instance

lemma graph_even : ∀ v, Even (graph.degree v) := by
  intro v
  fin_cases v <;> decide +kernel
lemma contracted_even : ∀ v, Even (contracted.degree v) := by
  intro v
  fin_cases v <;> decide +kernel
lemma graph_degree_one : graph.degree 1 = 6 := by decide +kernel
lemma contracted_degree_zero : contracted.degree 0 = 6 := by decide +kernel
lemma closing_adj : graph.Adj 0 15 := by decide +kernel

def basePath0 : ThreeCycleObstruction.exampleGraph.Walk 0 1 :=
  (.cons (show ThreeCycleObstruction.exampleGraph.Adj 0 7 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 7 3 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 3 2 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 2 4 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 4 9 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 9 11 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 11 5 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 5 1 by decide +kernel) .nil))))))))

lemma basePath0_path : basePath0.IsPath := by
  rw [Walk.isPath_def]
  decide +kernel

def basePath1 : ThreeCycleObstruction.exampleGraph.Walk 0 1 :=
  (.cons (show ThreeCycleObstruction.exampleGraph.Adj 0 8 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 8 10 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 10 13 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 13 6 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 6 11 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 11 4 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 4 14 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 14 2 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 2 12 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 12 1 by decide +kernel) .nil))))))))))

lemma basePath1_path : basePath1.IsPath := by
  rw [Walk.isPath_def]
  decide +kernel

def basePath2 : ThreeCycleObstruction.exampleGraph.Walk 0 1 :=
  (.cons (show ThreeCycleObstruction.exampleGraph.Adj 0 9 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 9 7 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 7 13 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 13 3 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 3 12 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 12 5 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 5 6 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 6 10 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 10 14 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 14 8 by decide +kernel) (.cons (show ThreeCycleObstruction.exampleGraph.Adj 8 1 by decide +kernel) .nil)))))))))))

lemma basePath2_path : basePath2.IsPath := by
  rw [Walk.isPath_def]
  decide +kernel

lemma base_paths_cover : ∀ x y : Fin 15,
    (ThreeCycleObstruction.exampleGraph.Adj x y ∧ s(x,y) ≠ s(0,1)) ↔
    s(x,y) ∈ basePath0.edges ∨ s(x,y) ∈ basePath1.edges ∨ s(x,y) ∈ basePath2.edges := by decide +kernel

lemma base_paths_disjoint : basePath0.edges.Disjoint basePath1.edges ∧
    basePath0.edges.Disjoint basePath2.edges ∧ basePath1.edges.Disjoint basePath2.edges := by
  simp only [List.disjoint_iff_ne,basePath0,basePath1,basePath2,Walk.edges_cons,Walk.edges_nil,
    List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  repeat' apply And.intro
  all_goals decide +kernel

def u0 : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 8 by decide +kernel) (.cons (show graph.Adj 8 1 by decide +kernel) (.cons (show graph.Adj 1 22 by decide +kernel) (.cons (show graph.Adj 22 15 by decide +kernel) (.cons (show graph.Adj 15 0 by decide +kernel) .nil)))))

lemma u0_cycle : u0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def u1 : graph.Walk 0 0 :=
  (.cons (show graph.Adj 0 7 by decide +kernel) (.cons (show graph.Adj 7 3 by decide +kernel) (.cons (show graph.Adj 3 2 by decide +kernel) (.cons (show graph.Adj 2 12 by decide +kernel) (.cons (show graph.Adj 12 1 by decide +kernel) (.cons (show graph.Adj 1 5 by decide +kernel) (.cons (show graph.Adj 5 6 by decide +kernel) (.cons (show graph.Adj 6 13 by decide +kernel) (.cons (show graph.Adj 13 10 by decide +kernel) (.cons (show graph.Adj 10 14 by decide +kernel) (.cons (show graph.Adj 14 4 by decide +kernel) (.cons (show graph.Adj 4 11 by decide +kernel) (.cons (show graph.Adj 11 9 by decide +kernel) (.cons (show graph.Adj 9 0 by decide +kernel) .nil))))))))))))))

lemma u1_cycle : u1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def u2 : graph.Walk 2 2 :=
  (.cons (show graph.Adj 2 4 by decide +kernel) (.cons (show graph.Adj 4 9 by decide +kernel) (.cons (show graph.Adj 9 7 by decide +kernel) (.cons (show graph.Adj 7 13 by decide +kernel) (.cons (show graph.Adj 13 3 by decide +kernel) (.cons (show graph.Adj 3 12 by decide +kernel) (.cons (show graph.Adj 12 5 by decide +kernel) (.cons (show graph.Adj 5 11 by decide +kernel) (.cons (show graph.Adj 11 6 by decide +kernel) (.cons (show graph.Adj 6 10 by decide +kernel) (.cons (show graph.Adj 10 8 by decide +kernel) (.cons (show graph.Adj 8 14 by decide +kernel) (.cons (show graph.Adj 14 2 by decide +kernel) .nil)))))))))))))

lemma u2_cycle : u2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def u3 : graph.Walk 1 1 :=
  (.cons (show graph.Adj 1 21 by decide +kernel) (.cons (show graph.Adj 21 17 by decide +kernel) (.cons (show graph.Adj 17 16 by decide +kernel) (.cons (show graph.Adj 16 26 by decide +kernel) (.cons (show graph.Adj 26 15 by decide +kernel) (.cons (show graph.Adj 15 19 by decide +kernel) (.cons (show graph.Adj 19 20 by decide +kernel) (.cons (show graph.Adj 20 27 by decide +kernel) (.cons (show graph.Adj 27 24 by decide +kernel) (.cons (show graph.Adj 24 28 by decide +kernel) (.cons (show graph.Adj 28 18 by decide +kernel) (.cons (show graph.Adj 18 25 by decide +kernel) (.cons (show graph.Adj 25 23 by decide +kernel) (.cons (show graph.Adj 23 1 by decide +kernel) .nil))))))))))))))

lemma u3_cycle : u3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def u4 : graph.Walk 16 16 :=
  (.cons (show graph.Adj 16 18 by decide +kernel) (.cons (show graph.Adj 18 23 by decide +kernel) (.cons (show graph.Adj 23 21 by decide +kernel) (.cons (show graph.Adj 21 27 by decide +kernel) (.cons (show graph.Adj 27 17 by decide +kernel) (.cons (show graph.Adj 17 26 by decide +kernel) (.cons (show graph.Adj 26 19 by decide +kernel) (.cons (show graph.Adj 19 25 by decide +kernel) (.cons (show graph.Adj 25 20 by decide +kernel) (.cons (show graph.Adj 20 24 by decide +kernel) (.cons (show graph.Adj 24 22 by decide +kernel) (.cons (show graph.Adj 22 28 by decide +kernel) (.cons (show graph.Adj 28 16 by decide +kernel) .nil)))))))))))))

lemma u4_cycle : u4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide +kernel

def uroot : Fin 5 → Fin 29 := ![0,0,2,1,16]
def uwalk : ∀ i : Fin 5, graph.Walk (uroot i) (uroot i)
  | 0 => u0
  | 1 => u1
  | 2 => u2
  | 3 => u3
  | 4 => u4

lemma uwalk_cycle (i : Fin 5) : (uwalk i).IsCycle := by
  fin_cases i
  · exact u0_cycle
  · exact u1_cycle
  · exact u2_cycle
  · exact u3_cycle
  · exact u4_cycle

lemma uwalk_disjoint : ∀ i j : Fin 5, i ≠ j →
    Disjoint (uwalk i).edges.toFinset (uwalk j).edges.toFinset := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | skip
  all_goals
    simp only [uwalk,u0,u1,u2,u3,u4,
      Walk.edges_cons,Walk.edges_nil,List.disjoint_toFinset_iff_disjoint,List.disjoint_iff_ne,
      List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
    repeat' apply And.intro
    all_goals decide +kernel

lemma uwalk_cover : ∀ x y : Fin 29, graph.Adj x y ↔
    ∃ i : Fin 5, s(x,y) ∈ (uwalk i).edges.toFinset := by
  simp only [List.mem_toFinset]
  decide +kernel

lemma graph_upper : number graph ≤ 5 := by
  have h := DiminishingReturns.number_le_cycle_family uroot uwalk uwalk_cycle
    (by simpa only [List.disjoint_toFinset_iff_disjoint] using uwalk_disjoint)
    (by simpa only [List.mem_toFinset] using uwalk_cover)
  simpa only [Fintype.card_fin] using h


end Erdos184Work.ContractionGap
