import Submission.CyclePartitionLift

/-! Checked cycle-partition certificates for the 27 cyclic-order choices of
three cycles with two separate contacts per pair. Each kernel has six junctions
and twelve labelled paths, and admits at least four cycle pieces. This file
asserts path-substitution certificates, not extraction of arbitrary layouts. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DoubleTripleCertificates
open PathSubstitution
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace Layout0
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,1,4,5,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,1,4,5,0,3,4,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{7,11,1,0},{8,2},{4,5,9,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,2),s(2,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,2) then 11 else
  if d.edge = s(2,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 5 by decide) (.cons (show p0Graph.Adj 5 2 by decide) (.cons (show p0Graph.Adj 2 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,4),s(4,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 1 by decide) (.cons (show p2Graph.Adj 1 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil))))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout0

namespace Layout1
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,1,4,5,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,1,4,5,0,3,5,4,2]
def parts : Fin 5 → Finset (Fin 12) := ![{4,0},{5,11,1},{8,2},{7,9,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,2) then 11 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 9 else
  3
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 5 by decide) (.cons (show p3Graph.Adj 5 3 by decide) (.cons (show p3Graph.Adj 3 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit4 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit4_labels : (circuit4 F hs ht).labels = parts 4 := by
  dsimp only [circuit4,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 5 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht,circuit4 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
    · exact circuit4_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout1

namespace Layout2
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,1,4,5,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,1,4,5,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,0},{5,9,2,1},{7,10,3},{11,6,8}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,3),s(3,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  if d.edge = s(3,2) then 2 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 3 by decide) (.cons (show p1Graph.Adj 3 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil))))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 10 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 5 by decide) (.cons (show p2Graph.Adj 5 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(2,5),s(5,4),s(4,2)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(2,5) then 11 else
  if d.edge = s(5,4) then 6 else
  8
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 2 2 := .cons (show p3Graph.Adj 2 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 2 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout2

namespace Layout3
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,1,5,4,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,1,5,4,0,3,4,5,2]
def parts : Fin 5 → Finset (Fin 12) := ![{4,0},{5,11,1},{8,2},{7,9,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,2) then 11 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,3),s(3,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,3) then 9 else
  3
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 4 by decide) (.cons (show p3Graph.Adj 4 3 by decide) (.cons (show p3Graph.Adj 3 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit4 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit4_labels : (circuit4 F hs ht).labels = parts 4 := by
  dsimp only [circuit4,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 5 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht,circuit4 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
    · exact circuit4_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout3

namespace Layout4
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,1,5,4,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,1,5,4,0,3,5,4,2]
def parts : Fin 4 → Finset (Fin 12) := ![{7,11,1,0},{8,2},{4,5,9,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,2),s(2,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,2) then 11 else
  if d.edge = s(2,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 4 by decide) (.cons (show p0Graph.Adj 4 2 by decide) (.cons (show p0Graph.Adj 2 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,5),s(5,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 1 by decide) (.cons (show p2Graph.Adj 1 5 by decide) (.cons (show p2Graph.Adj 5 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil))))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout4

namespace Layout5
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,1,5,4,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,1,5,4,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,0},{5,10,2,1},{7,9,3},{11,6,8}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,3),s(3,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,3) then 10 else
  if d.edge = s(3,2) then 2 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 3 by decide) (.cons (show p1Graph.Adj 3 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil))))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(2,5),s(5,4),s(4,2)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(2,5) then 11 else
  if d.edge = s(5,4) then 6 else
  8
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 2 2 := .cons (show p3Graph.Adj 2 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 2 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout5

namespace Layout6
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,4,1,5,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,4,1,5,0,3,4,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{7,11,1,0},{8,2},{4,9,3},{6,10,5}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,2),s(2,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,2) then 11 else
  if d.edge = s(2,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 5 by decide) (.cons (show p0Graph.Adj 5 2 by decide) (.cons (show p0Graph.Adj 2 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,4),s(4,1)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,4) then 10 else
  5
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 1 1 := .cons (show p3Graph.Adj 1 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 1 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout6

namespace Layout7
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,4,1,5,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,4,1,5,0,3,5,4,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,11,1,0},{8,2},{7,9,3},{6,10,5}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,2),s(2,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,2) then 11 else
  if d.edge = s(2,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 4 by decide) (.cons (show p0Graph.Adj 4 2 by decide) (.cons (show p0Graph.Adj 2 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 5 by decide) (.cons (show p2Graph.Adj 5 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,4),s(4,1)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,4) then 10 else
  5
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 1 1 := .cons (show p3Graph.Adj 1 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 1 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout7

namespace Layout8
def src : Fin 12 → Fin 6 := ![0,1,2,3,0,4,1,5,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![1,2,3,0,4,1,5,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,5,0},{6,11,1},{8,9,2},{7,10,3}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,1) then 5 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 4 by decide) (.cons (show p0Graph.Adj 4 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,2) then 11 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(2,4),s(4,3),s(3,2)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(2,4) then 8 else
  if d.edge = s(4,3) then 9 else
  2
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 2 2 := .cons (show p2Graph.Adj 2 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 2 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 10 else
  3
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 5 by decide) (.cons (show p3Graph.Adj 5 3 by decide) (.cons (show p3Graph.Adj 3 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout8

namespace Layout9
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,1,4,5,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,1,4,5,0,3,4,5,2]
def parts : Fin 5 → Finset (Fin 12) := ![{4,0},{5,9,1},{8,2},{7,11,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,2),s(2,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,2) then 11 else
  3
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 5 by decide) (.cons (show p3Graph.Adj 5 2 by decide) (.cons (show p3Graph.Adj 2 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit4 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit4_labels : (circuit4 F hs ht).labels = parts 4 := by
  dsimp only [circuit4,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 5 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht,circuit4 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
    · exact circuit4_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout9

namespace Layout10
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,1,4,5,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,1,4,5,0,3,5,4,2]
def parts : Fin 4 → Finset (Fin 12) := ![{7,9,1,0},{8,2},{4,5,11,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 9 else
  if d.edge = s(3,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 5 by decide) (.cons (show p0Graph.Adj 5 3 by decide) (.cons (show p0Graph.Adj 3 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,4),s(4,2),s(2,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,2) then 11 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 1 by decide) (.cons (show p2Graph.Adj 1 4 by decide) (.cons (show p2Graph.Adj 4 2 by decide) (.cons (show p2Graph.Adj 2 0 by decide) (.nil))))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout10

namespace Layout11
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,1,4,5,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,1,4,5,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,0},{5,8,2,1},{7,11,3},{10,6,9}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,2),s(2,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,2) then 8 else
  if d.edge = s(2,3) then 2 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 2 by decide) (.cons (show p1Graph.Adj 2 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil))))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,2),s(2,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,2) then 11 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 5 by decide) (.cons (show p2Graph.Adj 5 2 by decide) (.cons (show p2Graph.Adj 2 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(3,5),s(5,4),s(4,3)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(3,5) then 10 else
  if d.edge = s(5,4) then 6 else
  9
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 3 3 := .cons (show p3Graph.Adj 3 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 3 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout11

namespace Layout12
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,1,5,4,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,1,5,4,0,3,4,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{7,9,1,0},{8,2},{4,5,11,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,3),s(3,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,3) then 9 else
  if d.edge = s(3,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 4 by decide) (.cons (show p0Graph.Adj 4 3 by decide) (.cons (show p0Graph.Adj 3 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,5),s(5,2),s(2,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,2) then 11 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 1 by decide) (.cons (show p2Graph.Adj 1 5 by decide) (.cons (show p2Graph.Adj 5 2 by decide) (.cons (show p2Graph.Adj 2 0 by decide) (.nil))))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout12

namespace Layout13
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,1,5,4,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,1,5,4,0,3,5,4,2]
def parts : Fin 5 → Finset (Fin 12) := ![{4,0},{5,9,1},{8,2},{7,11,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,3) then 9 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,2),s(2,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,2) then 11 else
  3
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 4 by decide) (.cons (show p3Graph.Adj 4 2 by decide) (.cons (show p3Graph.Adj 2 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit4 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit4_labels : (circuit4 F hs ht).labels = parts 4 := by
  dsimp only [circuit4,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 5 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht,circuit4 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
    · exact circuit4_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout13

namespace Layout14
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,1,5,4,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,1,5,4,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,0},{5,11,2,1},{7,8,3},{10,6,9}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,2),s(2,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,2) then 11 else
  if d.edge = s(2,3) then 2 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 2 by decide) (.cons (show p1Graph.Adj 2 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil))))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,2),s(2,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,2) then 8 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 4 by decide) (.cons (show p2Graph.Adj 4 2 by decide) (.cons (show p2Graph.Adj 2 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(3,5),s(5,4),s(4,3)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(3,5) then 10 else
  if d.edge = s(5,4) then 6 else
  9
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 3 3 := .cons (show p3Graph.Adj 3 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 3 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofParallel F 4 0 (by decide) (by rw [hs,ht]; decide)
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout14

namespace Layout15
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,4,1,5,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,4,1,5,0,3,4,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,9,1,0},{8,2},{7,11,3},{6,10,5}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,3),s(3,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,3) then 9 else
  if d.edge = s(3,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 4 by decide) (.cons (show p0Graph.Adj 4 3 by decide) (.cons (show p0Graph.Adj 3 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,2),s(2,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,2) then 11 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 5 by decide) (.cons (show p2Graph.Adj 5 2 by decide) (.cons (show p2Graph.Adj 2 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,4),s(4,1)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,4) then 10 else
  5
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 1 1 := .cons (show p3Graph.Adj 1 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 1 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout15

namespace Layout16
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,4,1,5,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,4,1,5,0,3,5,4,2]
def parts : Fin 4 → Finset (Fin 12) := ![{7,9,1,0},{8,2},{4,11,3},{6,10,5}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 9 else
  if d.edge = s(3,1) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 5 by decide) (.cons (show p0Graph.Adj 5 3 by decide) (.cons (show p0Graph.Adj 3 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil))))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,2),s(2,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,2) then 11 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 4 by decide) (.cons (show p2Graph.Adj 4 2 by decide) (.cons (show p2Graph.Adj 2 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,4),s(4,1)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,4) then 10 else
  5
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 1 1 := .cons (show p3Graph.Adj 1 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 1 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofParallel F 8 2 (by decide) (by rw [hs,ht]; decide)
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout16

namespace Layout17
def src : Fin 12 → Fin 6 := ![0,1,3,2,0,4,1,5,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![1,3,2,0,4,1,5,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,5,0},{6,10,1},{8,9,2},{7,11,3}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,1),s(1,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,1) then 5 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 4 by decide) (.cons (show p0Graph.Adj 4 1 by decide) (.cons (show p0Graph.Adj 1 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,3) then 10 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(2,4),s(4,3),s(3,2)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(2,4) then 8 else
  if d.edge = s(4,3) then 9 else
  2
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 2 2 := .cons (show p2Graph.Adj 2 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 2 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,2),s(2,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,2) then 11 else
  3
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 5 by decide) (.cons (show p3Graph.Adj 5 2 by decide) (.cons (show p3Graph.Adj 2 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout17

namespace Layout18
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,1,4,5,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,1,4,5,0,3,4,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,1,0},{5,9,2},{7,11,8,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 1 by decide) (.cons (show p0Graph.Adj 1 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  2
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,2),s(2,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,2) then 11 else
  if d.edge = s(2,3) then 8 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 5 by decide) (.cons (show p2Graph.Adj 5 2 by decide) (.cons (show p2Graph.Adj 2 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil))))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout18

namespace Layout19
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,1,4,5,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,1,4,5,0,3,5,4,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,1,0},{5,11,8,2},{7,9,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 1 by decide) (.cons (show p0Graph.Adj 1 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,2),s(2,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,2) then 11 else
  if d.edge = s(2,3) then 8 else
  2
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 2 by decide) (.cons (show p1Graph.Adj 2 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil))))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 5 by decide) (.cons (show p2Graph.Adj 5 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout19

namespace Layout20
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,1,4,5,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,1,4,5,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,1,0},{5,9,2},{7,10,3},{11,6,8}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 1 by decide) (.cons (show p0Graph.Adj 1 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  2
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 10 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 5 by decide) (.cons (show p2Graph.Adj 5 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(2,5),s(5,4),s(4,2)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(2,5) then 11 else
  if d.edge = s(5,4) then 6 else
  8
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 2 2 := .cons (show p3Graph.Adj 2 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 2 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout20

namespace Layout21
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,1,5,4,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,1,5,4,0,3,4,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,1,0},{5,11,8,2},{7,9,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 1 by decide) (.cons (show p0Graph.Adj 1 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,2),s(2,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,2) then 11 else
  if d.edge = s(2,3) then 8 else
  2
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 2 by decide) (.cons (show p1Graph.Adj 2 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil))))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout21

namespace Layout22
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,1,5,4,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,1,5,4,0,3,5,4,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,1,0},{5,9,2},{7,11,8,3},{10,6}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 1 by decide) (.cons (show p0Graph.Adj 1 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,3) then 9 else
  2
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,2),s(2,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,2) then 11 else
  if d.edge = s(2,3) then 8 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 4 by decide) (.cons (show p2Graph.Adj 4 2 by decide) (.cons (show p2Graph.Adj 2 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil))))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofParallel F 10 6 (by decide) (by rw [hs,ht]; decide)
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofParallel]
  ext j
  simp only [Finset.mem_insert,Finset.mem_singleton]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout22

namespace Layout23
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,1,5,4,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,1,5,4,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,1,0},{5,10,2},{7,9,3},{11,6,8}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,1),s(1,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 1 by decide) (.cons (show p0Graph.Adj 1 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,3),s(3,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 5 else
  if d.edge = s(5,3) then 10 else
  2
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 3 by decide) (.cons (show p1Graph.Adj 3 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,3),s(3,0)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 7 else
  if d.edge = s(4,3) then 9 else
  3
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 0 0 := .cons (show p2Graph.Adj 0 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 0 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(2,5),s(5,4),s(4,2)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(2,5) then 11 else
  if d.edge = s(5,4) then 6 else
  8
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 2 2 := .cons (show p3Graph.Adj 2 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 2 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout23

namespace Layout24
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,4,1,5,2,3,4,5]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,4,1,5,0,3,4,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{3,8,0},{6,11,1},{5,9,2},{7,10,4}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,3),s(3,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,3) then 3 else
  if d.edge = s(3,2) then 8 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 3 by decide) (.cons (show p0Graph.Adj 3 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,2) then 11 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,3),s(3,1)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  2
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 1 1 := .cons (show p2Graph.Adj 1 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 1 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,4),s(4,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,4) then 10 else
  4
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout24

namespace Layout25
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,4,1,5,2,3,5,4]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,4,1,5,0,3,5,4,2]
def parts : Fin 4 → Finset (Fin 12) := ![{3,8,0},{5,11,1},{6,9,2},{7,10,4}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,3),s(3,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,3) then 3 else
  if d.edge = s(3,2) then 8 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 3 by decide) (.cons (show p0Graph.Adj 3 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,2) then 11 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 4 by decide) (.cons (show p1Graph.Adj 4 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,3),s(3,1)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,3) then 9 else
  2
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 1 1 := .cons (show p2Graph.Adj 1 5 by decide) (.cons (show p2Graph.Adj 5 3 by decide) (.cons (show p2Graph.Adj 3 1 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,4),s(4,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,4) then 10 else
  4
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 5 by decide) (.cons (show p3Graph.Adj 5 4 by decide) (.cons (show p3Graph.Adj 4 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout25

namespace Layout26
def src : Fin 12 → Fin 6 := ![0,2,1,3,0,4,1,5,2,4,3,5]
def dst : Fin 12 → Fin 6 := ![2,1,3,0,4,1,5,0,4,3,5,2]
def parts : Fin 4 → Finset (Fin 12) := ![{4,8,0},{6,11,1},{5,9,2},{7,10,3}]
lemma parts_disjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
lemma parts_cover : ∀ j, ∃ i, j ∈ parts i := by decide

def p0Edges : Finset (Sym2 (Fin 6)) := {s(0,4),s(4,2),s(2,0)}
def p0Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p0Edges
instance : DecidableRel p0Graph.Adj := by unfold p0Graph; infer_instance
def p0Route (d : p0Graph.Dart) : Fin 12 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,2) then 8 else
  0
lemma p0Ends : ∀ d, s(src (p0Route d),dst (p0Route d)) = d.edge := by decide
def p0Walk : p0Graph.Walk 0 0 := .cons (show p0Graph.Adj 0 4 by decide) (.cons (show p0Graph.Adj 4 2 by decide) (.cons (show p0Graph.Adj 2 0 by decide) (.nil)))
lemma p0Cycle : p0Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p1Edges : Finset (Sym2 (Fin 6)) := {s(1,5),s(5,2),s(2,1)}
def p1Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p1Edges
instance : DecidableRel p1Graph.Adj := by unfold p1Graph; infer_instance
def p1Route (d : p1Graph.Dart) : Fin 12 :=
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,2) then 11 else
  1
lemma p1Ends : ∀ d, s(src (p1Route d),dst (p1Route d)) = d.edge := by decide
def p1Walk : p1Graph.Walk 1 1 := .cons (show p1Graph.Adj 1 5 by decide) (.cons (show p1Graph.Adj 5 2 by decide) (.cons (show p1Graph.Adj 2 1 by decide) (.nil)))
lemma p1Cycle : p1Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p2Edges : Finset (Sym2 (Fin 6)) := {s(1,4),s(4,3),s(3,1)}
def p2Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p2Edges
instance : DecidableRel p2Graph.Adj := by unfold p2Graph; infer_instance
def p2Route (d : p2Graph.Dart) : Fin 12 :=
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  2
lemma p2Ends : ∀ d, s(src (p2Route d),dst (p2Route d)) = d.edge := by decide
def p2Walk : p2Graph.Walk 1 1 := .cons (show p2Graph.Adj 1 4 by decide) (.cons (show p2Graph.Adj 4 3 by decide) (.cons (show p2Graph.Adj 3 1 by decide) (.nil)))
lemma p2Cycle : p2Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def p3Edges : Finset (Sym2 (Fin 6)) := {s(0,5),s(5,3),s(3,0)}
def p3Graph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet p3Edges
instance : DecidableRel p3Graph.Adj := by unfold p3Graph; infer_instance
def p3Route (d : p3Graph.Dart) : Fin 12 :=
  if d.edge = s(0,5) then 7 else
  if d.edge = s(5,3) then 10 else
  3
lemma p3Ends : ∀ d, s(src (p3Route d),dst (p3Route d)) = d.edge := by decide
def p3Walk : p3Graph.Walk 0 0 := .cons (show p3Graph.Adj 0 5 by decide) (.cons (show p3Graph.Adj 5 3 by decide) (.cons (show p3Graph.Adj 3 0 by decide) (.nil)))
lemma p3Cycle : p3Walk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

section Realization
variable {V : Type*} [instV : Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
noncomputable def circuit0 : Family.Circuit F :=
  Family.Circuit.ofModel F p0Graph p0Route
    (fun d => by rw [hs,ht]; exact p0Ends d) p0Walk p0Cycle
lemma circuit0_labels : (circuit0 F hs ht).labels = parts 0 := by
  dsimp only [circuit0,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit1 : Family.Circuit F :=
  Family.Circuit.ofModel F p1Graph p1Route
    (fun d => by rw [hs,ht]; exact p1Ends d) p1Walk p1Cycle
lemma circuit1_labels : (circuit1 F hs ht).labels = parts 1 := by
  dsimp only [circuit1,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit2 : Family.Circuit F :=
  Family.Circuit.ofModel F p2Graph p2Route
    (fun d => by rw [hs,ht]; exact p2Ends d) p2Walk p2Cycle
lemma circuit2_labels : (circuit2 F hs ht).labels = parts 2 := by
  dsimp only [circuit2,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide
noncomputable def circuit3 : Family.Circuit F :=
  Family.Circuit.ofModel F p3Graph p3Route
    (fun d => by rw [hs,ht]; exact p3Ends d) p3Walk p3Cycle
lemma circuit3_labels : (circuit3 F hs ht).labels = parts 3 := by
  dsimp only [circuit3,Family.Circuit.ofModel]
  ext j
  simp only [List.mem_toFinset]
  revert j
  decide

include instV hs ht in
lemma subdivision_at_least_four
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Erdos184Work.IsDecomposition G D ∧ 4 ≤ D.card := by
  let C : Fin 4 → Family.Circuit F := ![circuit0 F hs ht,circuit1 F hs ht,circuit2 F hs ht,circuit3 F hs ht]
  have hc : ∀ i, (C i).labels = parts i := by
    intro i
    fin_cases i
    · exact circuit0_labels F hs ht
    · exact circuit1_labels F hs ht
    · exact circuit2_labels F hs ht
    · exact circuit3_labels F hs ht
  obtain ⟨D,hD,hdD,hcard⟩ := Family.Circuit.decomposition F C (by
    intro i j hij
    rw [hc i,hc j]
    exact parts_disjoint i j hij) (by
    intro j
    obtain ⟨i,hi⟩ := parts_cover j
    exact ⟨i,(hc i).symm ▸ hi⟩) hcover
  exact ⟨D,hD,hdD,by rw [hcard]; decide⟩

end Realization
#print axioms subdivision_at_least_four
end Layout26

end Erdos184Work.DoubleTripleCertificates
