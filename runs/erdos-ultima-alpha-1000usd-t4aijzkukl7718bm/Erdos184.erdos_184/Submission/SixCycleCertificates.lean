import Submission.RigidityDegree

/-! Two-cycle certificates for thirteen six-cycle junction layouts.
Each conclusion allows arbitrary internally disjoint path substitutions.
Completeness of the thirteen-layout list is NOT asserted here. This file
is an auxiliary finite result, not a proof of Erdős 184 or core rigidity. -/

open SimpleGraph
namespace Erdos184Work.SixCycleCertificates
open PathSubstitution
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Layout0
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,5,10,11,2,6,13,9,12,3,7,10,12,14,4,11,13,8,14]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,5,10,11,1,6,13,9,12,2,7,10,12,14,3,11,13,8,14,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,2), s(2,4), s(4,11), s(11,13), s(13,9), s(9,5), s(5,6), s(6,7), s(7,10), s(10,12), s(12,14), s(14,8), s(8,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,2) then 2 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,11) then 25 else
  if d.edge = s(11,13) then 26 else
  if d.edge = s(13,9) then 17 else
  if d.edge = s(9,5) then 11 else
  if d.edge = s(5,6) then 6 else
  if d.edge = s(6,7) then 7 else
  if d.edge = s(7,10) then 21 else
  if d.edge = s(10,12) then 22 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,8) then 28 else
  9
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 2 by decide) (.cons (show redGraph.Adj 2 4 by decide) (.cons (show redGraph.Adj 4 11 by decide) (.cons (show redGraph.Adj 11 13 by decide) (.cons (show redGraph.Adj 13 9 by decide) (.cons (show redGraph.Adj 9 5 by decide) (.cons (show redGraph.Adj 5 6 by decide) (.cons (show redGraph.Adj 6 7 by decide) (.cons (show redGraph.Adj 7 10 by decide) (.cons (show redGraph.Adj 10 12 by decide) (.cons (show redGraph.Adj 12 14 by decide) (.cons (show redGraph.Adj 14 8 by decide) (.cons (show redGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,4), s(4,14), s(14,3), s(3,7), s(7,8), s(8,13), s(13,6), s(6,2), s(2,12), s(12,9), s(9,1), s(1,11), s(11,10), s(10,5), s(5,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,14) then 29 else
  if d.edge = s(14,3) then 24 else
  if d.edge = s(3,7) then 20 else
  if d.edge = s(7,8) then 8 else
  if d.edge = s(8,13) then 27 else
  if d.edge = s(13,6) then 16 else
  if d.edge = s(6,2) then 15 else
  if d.edge = s(2,12) then 19 else
  if d.edge = s(12,9) then 18 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,11) then 14 else
  if d.edge = s(11,10) then 13 else
  if d.edge = s(10,5) then 12 else
  5
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 4 by decide) (.cons (show blueGraph.Adj 4 14 by decide) (.cons (show blueGraph.Adj 14 3 by decide) (.cons (show blueGraph.Adj 3 7 by decide) (.cons (show blueGraph.Adj 7 8 by decide) (.cons (show blueGraph.Adj 8 13 by decide) (.cons (show blueGraph.Adj 13 6 by decide) (.cons (show blueGraph.Adj 6 2 by decide) (.cons (show blueGraph.Adj 2 12 by decide) (.cons (show blueGraph.Adj 12 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 11 by decide) (.cons (show blueGraph.Adj 11 10 by decide) (.cons (show blueGraph.Adj 10 5 by decide) (.cons (show blueGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout0

namespace Layout1
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,5,11,10,2,6,13,9,12,3,7,10,12,14,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,5,11,10,1,6,13,9,12,2,7,10,12,14,3,11,14,8,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,2), s(2,4), s(4,11), s(11,5), s(5,9), s(9,13), s(13,6), s(6,7), s(7,10), s(10,12), s(12,14), s(14,8), s(8,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,2) then 2 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,11) then 25 else
  if d.edge = s(11,5) then 12 else
  if d.edge = s(5,9) then 11 else
  if d.edge = s(9,13) then 17 else
  if d.edge = s(13,6) then 16 else
  if d.edge = s(6,7) then 7 else
  if d.edge = s(7,10) then 21 else
  if d.edge = s(10,12) then 22 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,8) then 27 else
  9
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 2 by decide) (.cons (show redGraph.Adj 2 4 by decide) (.cons (show redGraph.Adj 4 11 by decide) (.cons (show redGraph.Adj 11 5 by decide) (.cons (show redGraph.Adj 5 9 by decide) (.cons (show redGraph.Adj 9 13 by decide) (.cons (show redGraph.Adj 13 6 by decide) (.cons (show redGraph.Adj 6 7 by decide) (.cons (show redGraph.Adj 7 10 by decide) (.cons (show redGraph.Adj 10 12 by decide) (.cons (show redGraph.Adj 12 14 by decide) (.cons (show redGraph.Adj 14 8 by decide) (.cons (show redGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,4), s(4,13), s(13,8), s(8,7), s(7,3), s(3,14), s(14,11), s(11,10), s(10,1), s(1,9), s(9,12), s(12,2), s(2,6), s(6,5), s(5,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,13) then 29 else
  if d.edge = s(13,8) then 28 else
  if d.edge = s(8,7) then 8 else
  if d.edge = s(7,3) then 20 else
  if d.edge = s(3,14) then 24 else
  if d.edge = s(14,11) then 26 else
  if d.edge = s(11,10) then 13 else
  if d.edge = s(10,1) then 14 else
  if d.edge = s(1,9) then 10 else
  if d.edge = s(9,12) then 18 else
  if d.edge = s(12,2) then 19 else
  if d.edge = s(2,6) then 15 else
  if d.edge = s(6,5) then 6 else
  5
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 4 by decide) (.cons (show blueGraph.Adj 4 13 by decide) (.cons (show blueGraph.Adj 13 8 by decide) (.cons (show blueGraph.Adj 8 7 by decide) (.cons (show blueGraph.Adj 7 3 by decide) (.cons (show blueGraph.Adj 3 14 by decide) (.cons (show blueGraph.Adj 14 11 by decide) (.cons (show blueGraph.Adj 11 10 by decide) (.cons (show blueGraph.Adj 10 1 by decide) (.cons (show blueGraph.Adj 1 9 by decide) (.cons (show blueGraph.Adj 9 12 by decide) (.cons (show blueGraph.Adj 12 2 by decide) (.cons (show blueGraph.Adj 2 6 by decide) (.cons (show blueGraph.Adj 6 5 by decide) (.cons (show blueGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout1

namespace Layout2
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,11,5,10,2,6,9,13,12,3,7,10,12,14,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,11,5,10,1,6,9,13,12,2,7,10,12,14,3,11,14,8,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,2), s(2,4), s(4,11), s(11,5), s(5,10), s(10,7), s(7,6), s(6,9), s(9,13), s(13,12), s(12,14), s(14,8), s(8,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,2) then 2 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,11) then 25 else
  if d.edge = s(11,5) then 12 else
  if d.edge = s(5,10) then 13 else
  if d.edge = s(10,7) then 21 else
  if d.edge = s(7,6) then 7 else
  if d.edge = s(6,9) then 16 else
  if d.edge = s(9,13) then 17 else
  if d.edge = s(13,12) then 18 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,8) then 27 else
  9
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 2 by decide) (.cons (show redGraph.Adj 2 4 by decide) (.cons (show redGraph.Adj 4 11 by decide) (.cons (show redGraph.Adj 11 5 by decide) (.cons (show redGraph.Adj 5 10 by decide) (.cons (show redGraph.Adj 10 7 by decide) (.cons (show redGraph.Adj 7 6 by decide) (.cons (show redGraph.Adj 6 9 by decide) (.cons (show redGraph.Adj 9 13 by decide) (.cons (show redGraph.Adj 13 12 by decide) (.cons (show redGraph.Adj 12 14 by decide) (.cons (show redGraph.Adj 14 8 by decide) (.cons (show redGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,4), s(4,13), s(13,8), s(8,7), s(7,3), s(3,14), s(14,11), s(11,9), s(9,1), s(1,10), s(10,12), s(12,2), s(2,6), s(6,5), s(5,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,13) then 29 else
  if d.edge = s(13,8) then 28 else
  if d.edge = s(8,7) then 8 else
  if d.edge = s(7,3) then 20 else
  if d.edge = s(3,14) then 24 else
  if d.edge = s(14,11) then 26 else
  if d.edge = s(11,9) then 11 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,10) then 14 else
  if d.edge = s(10,12) then 22 else
  if d.edge = s(12,2) then 19 else
  if d.edge = s(2,6) then 15 else
  if d.edge = s(6,5) then 6 else
  5
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 4 by decide) (.cons (show blueGraph.Adj 4 13 by decide) (.cons (show blueGraph.Adj 13 8 by decide) (.cons (show blueGraph.Adj 8 7 by decide) (.cons (show blueGraph.Adj 7 3 by decide) (.cons (show blueGraph.Adj 3 14 by decide) (.cons (show blueGraph.Adj 14 11 by decide) (.cons (show blueGraph.Adj 11 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 10 by decide) (.cons (show blueGraph.Adj 10 12 by decide) (.cons (show blueGraph.Adj 12 2 by decide) (.cons (show blueGraph.Adj 2 6 by decide) (.cons (show blueGraph.Adj 6 5 by decide) (.cons (show blueGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout2

namespace Layout3
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,7,8,1,9,11,5,10,2,6,9,13,12,3,7,10,12,14,4,13,8,11,14]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,7,8,0,9,11,5,10,1,6,9,13,12,2,7,10,12,14,3,13,8,11,14,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,2), s(2,4), s(4,14), s(14,12), s(12,13), s(13,9), s(9,6), s(6,7), s(7,10), s(10,5), s(5,11), s(11,8), s(8,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,2) then 2 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,14) then 29 else
  if d.edge = s(14,12) then 23 else
  if d.edge = s(12,13) then 18 else
  if d.edge = s(13,9) then 17 else
  if d.edge = s(9,6) then 16 else
  if d.edge = s(6,7) then 7 else
  if d.edge = s(7,10) then 21 else
  if d.edge = s(10,5) then 13 else
  if d.edge = s(5,11) then 12 else
  if d.edge = s(11,8) then 27 else
  9
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 2 by decide) (.cons (show redGraph.Adj 2 4 by decide) (.cons (show redGraph.Adj 4 14 by decide) (.cons (show redGraph.Adj 14 12 by decide) (.cons (show redGraph.Adj 12 13 by decide) (.cons (show redGraph.Adj 13 9 by decide) (.cons (show redGraph.Adj 9 6 by decide) (.cons (show redGraph.Adj 6 7 by decide) (.cons (show redGraph.Adj 7 10 by decide) (.cons (show redGraph.Adj 10 5 by decide) (.cons (show redGraph.Adj 5 11 by decide) (.cons (show redGraph.Adj 11 8 by decide) (.cons (show redGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,4), s(4,13), s(13,8), s(8,7), s(7,3), s(3,14), s(14,11), s(11,9), s(9,1), s(1,10), s(10,12), s(12,2), s(2,6), s(6,5), s(5,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,13) then 25 else
  if d.edge = s(13,8) then 26 else
  if d.edge = s(8,7) then 8 else
  if d.edge = s(7,3) then 20 else
  if d.edge = s(3,14) then 24 else
  if d.edge = s(14,11) then 28 else
  if d.edge = s(11,9) then 11 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,10) then 14 else
  if d.edge = s(10,12) then 22 else
  if d.edge = s(12,2) then 19 else
  if d.edge = s(2,6) then 15 else
  if d.edge = s(6,5) then 6 else
  5
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 4 by decide) (.cons (show blueGraph.Adj 4 13 by decide) (.cons (show blueGraph.Adj 13 8 by decide) (.cons (show blueGraph.Adj 8 7 by decide) (.cons (show blueGraph.Adj 7 3 by decide) (.cons (show blueGraph.Adj 3 14 by decide) (.cons (show blueGraph.Adj 14 11 by decide) (.cons (show blueGraph.Adj 11 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 10 by decide) (.cons (show blueGraph.Adj 10 12 by decide) (.cons (show blueGraph.Adj 12 2 by decide) (.cons (show blueGraph.Adj 2 6 by decide) (.cons (show blueGraph.Adj 6 5 by decide) (.cons (show blueGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout3

namespace Layout4
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,6,8,7,1,9,11,5,10,2,6,9,13,12,3,7,10,12,14,4,13,8,11,14]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,6,8,7,0,9,11,5,10,1,6,9,13,12,2,7,10,12,14,3,13,8,11,14,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,2), s(2,4), s(4,14), s(14,12), s(12,13), s(13,8), s(8,11), s(11,9), s(9,6), s(6,5), s(5,10), s(10,7), s(7,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,2) then 2 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,14) then 29 else
  if d.edge = s(14,12) then 23 else
  if d.edge = s(12,13) then 18 else
  if d.edge = s(13,8) then 26 else
  if d.edge = s(8,11) then 27 else
  if d.edge = s(11,9) then 11 else
  if d.edge = s(9,6) then 16 else
  if d.edge = s(6,5) then 6 else
  if d.edge = s(5,10) then 13 else
  if d.edge = s(10,7) then 21 else
  9
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 2 by decide) (.cons (show redGraph.Adj 2 4 by decide) (.cons (show redGraph.Adj 4 14 by decide) (.cons (show redGraph.Adj 14 12 by decide) (.cons (show redGraph.Adj 12 13 by decide) (.cons (show redGraph.Adj 13 8 by decide) (.cons (show redGraph.Adj 8 11 by decide) (.cons (show redGraph.Adj 11 9 by decide) (.cons (show redGraph.Adj 9 6 by decide) (.cons (show redGraph.Adj 6 5 by decide) (.cons (show redGraph.Adj 5 10 by decide) (.cons (show redGraph.Adj 10 7 by decide) (.cons (show redGraph.Adj 7 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,4), s(4,13), s(13,9), s(9,1), s(1,10), s(10,12), s(12,2), s(2,6), s(6,8), s(8,7), s(7,3), s(3,14), s(14,11), s(11,5), s(5,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,13) then 25 else
  if d.edge = s(13,9) then 17 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,10) then 14 else
  if d.edge = s(10,12) then 22 else
  if d.edge = s(12,2) then 19 else
  if d.edge = s(2,6) then 15 else
  if d.edge = s(6,8) then 7 else
  if d.edge = s(8,7) then 8 else
  if d.edge = s(7,3) then 20 else
  if d.edge = s(3,14) then 24 else
  if d.edge = s(14,11) then 28 else
  if d.edge = s(11,5) then 12 else
  5
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 4 by decide) (.cons (show blueGraph.Adj 4 13 by decide) (.cons (show blueGraph.Adj 13 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 10 by decide) (.cons (show blueGraph.Adj 10 12 by decide) (.cons (show blueGraph.Adj 12 2 by decide) (.cons (show blueGraph.Adj 2 6 by decide) (.cons (show blueGraph.Adj 6 8 by decide) (.cons (show blueGraph.Adj 8 7 by decide) (.cons (show blueGraph.Adj 7 3 by decide) (.cons (show blueGraph.Adj 3 14 by decide) (.cons (show blueGraph.Adj 14 11 by decide) (.cons (show blueGraph.Adj 11 5 by decide) (.cons (show blueGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout4

namespace Layout5
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,8,6,7,1,9,5,10,11,2,6,9,13,12,3,12,10,7,14,4,11,8,14,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,8,6,7,0,9,5,10,11,1,6,9,13,12,2,12,10,7,14,3,11,8,14,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,2), s(2,12), s(12,13), s(13,9), s(9,6), s(6,7), s(7,14), s(14,8), s(8,5), s(5,10), s(10,11), s(11,4), s(4,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,2) then 2 else
  if d.edge = s(2,12) then 19 else
  if d.edge = s(12,13) then 18 else
  if d.edge = s(13,9) then 17 else
  if d.edge = s(9,6) then 16 else
  if d.edge = s(6,7) then 8 else
  if d.edge = s(7,14) then 23 else
  if d.edge = s(14,8) then 27 else
  if d.edge = s(8,5) then 6 else
  if d.edge = s(5,10) then 12 else
  if d.edge = s(10,11) then 13 else
  if d.edge = s(11,4) then 25 else
  4
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 2 by decide) (.cons (show redGraph.Adj 2 12 by decide) (.cons (show redGraph.Adj 12 13 by decide) (.cons (show redGraph.Adj 13 9 by decide) (.cons (show redGraph.Adj 9 6 by decide) (.cons (show redGraph.Adj 6 7 by decide) (.cons (show redGraph.Adj 7 14 by decide) (.cons (show redGraph.Adj 14 8 by decide) (.cons (show redGraph.Adj 8 5 by decide) (.cons (show redGraph.Adj 5 10 by decide) (.cons (show redGraph.Adj 10 11 by decide) (.cons (show redGraph.Adj 11 4 by decide) (.cons (show redGraph.Adj 4 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,5), s(5,9), s(9,1), s(1,11), s(11,8), s(8,6), s(6,2), s(2,4), s(4,13), s(13,14), s(14,3), s(3,12), s(12,10), s(10,7), s(7,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,5) then 5 else
  if d.edge = s(5,9) then 11 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,11) then 14 else
  if d.edge = s(11,8) then 26 else
  if d.edge = s(8,6) then 7 else
  if d.edge = s(6,2) then 15 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,13) then 29 else
  if d.edge = s(13,14) then 28 else
  if d.edge = s(14,3) then 24 else
  if d.edge = s(3,12) then 20 else
  if d.edge = s(12,10) then 21 else
  if d.edge = s(10,7) then 22 else
  9
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 5 by decide) (.cons (show blueGraph.Adj 5 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 11 by decide) (.cons (show blueGraph.Adj 11 8 by decide) (.cons (show blueGraph.Adj 8 6 by decide) (.cons (show blueGraph.Adj 6 2 by decide) (.cons (show blueGraph.Adj 2 4 by decide) (.cons (show blueGraph.Adj 4 13 by decide) (.cons (show blueGraph.Adj 13 14 by decide) (.cons (show blueGraph.Adj 14 3 by decide) (.cons (show blueGraph.Adj 3 12 by decide) (.cons (show blueGraph.Adj 12 10 by decide) (.cons (show blueGraph.Adj 10 7 by decide) (.cons (show blueGraph.Adj 7 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout5

namespace Layout6
def src : Fin 30 → Fin 15 := ![0,1,3,2,4,0,5,8,6,7,1,9,5,10,11,2,6,13,9,12,3,7,10,12,14,4,11,8,14,13]
def dst : Fin 30 → Fin 15 := ![1,3,2,4,0,5,8,6,7,0,9,5,10,11,1,6,13,9,12,2,7,10,12,14,3,11,8,14,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,2), s(2,4), s(4,11), s(11,10), s(10,12), s(12,14), s(14,13), s(13,9), s(9,5), s(5,8), s(8,6), s(6,7), s(7,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,2) then 2 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,11) then 25 else
  if d.edge = s(11,10) then 13 else
  if d.edge = s(10,12) then 22 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,13) then 28 else
  if d.edge = s(13,9) then 17 else
  if d.edge = s(9,5) then 11 else
  if d.edge = s(5,8) then 6 else
  if d.edge = s(8,6) then 7 else
  if d.edge = s(6,7) then 8 else
  9
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 2 by decide) (.cons (show redGraph.Adj 2 4 by decide) (.cons (show redGraph.Adj 4 11 by decide) (.cons (show redGraph.Adj 11 10 by decide) (.cons (show redGraph.Adj 10 12 by decide) (.cons (show redGraph.Adj 12 14 by decide) (.cons (show redGraph.Adj 14 13 by decide) (.cons (show redGraph.Adj 13 9 by decide) (.cons (show redGraph.Adj 9 5 by decide) (.cons (show redGraph.Adj 5 8 by decide) (.cons (show redGraph.Adj 8 6 by decide) (.cons (show redGraph.Adj 6 7 by decide) (.cons (show redGraph.Adj 7 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,4), s(4,13), s(13,6), s(6,2), s(2,12), s(12,9), s(9,1), s(1,11), s(11,8), s(8,14), s(14,3), s(3,7), s(7,10), s(10,5), s(5,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,13) then 29 else
  if d.edge = s(13,6) then 16 else
  if d.edge = s(6,2) then 15 else
  if d.edge = s(2,12) then 19 else
  if d.edge = s(12,9) then 18 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,11) then 14 else
  if d.edge = s(11,8) then 26 else
  if d.edge = s(8,14) then 27 else
  if d.edge = s(14,3) then 24 else
  if d.edge = s(3,7) then 20 else
  if d.edge = s(7,10) then 21 else
  if d.edge = s(10,5) then 12 else
  5
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 4 by decide) (.cons (show blueGraph.Adj 4 13 by decide) (.cons (show blueGraph.Adj 13 6 by decide) (.cons (show blueGraph.Adj 6 2 by decide) (.cons (show blueGraph.Adj 2 12 by decide) (.cons (show blueGraph.Adj 12 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 11 by decide) (.cons (show blueGraph.Adj 11 8 by decide) (.cons (show blueGraph.Adj 8 14 by decide) (.cons (show blueGraph.Adj 14 3 by decide) (.cons (show blueGraph.Adj 3 7 by decide) (.cons (show blueGraph.Adj 7 10 by decide) (.cons (show blueGraph.Adj 10 5 by decide) (.cons (show blueGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout6

namespace Layout7
def src : Fin 30 → Fin 15 := ![0,1,3,4,2,0,5,6,7,8,1,9,5,11,10,2,6,13,9,12,3,7,10,12,14,4,11,8,14,13]
def dst : Fin 30 → Fin 15 := ![1,3,4,2,0,5,6,7,8,0,9,5,11,10,1,6,13,9,12,2,7,10,12,14,3,11,8,14,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,4), s(4,2), s(2,12), s(12,9), s(9,13), s(13,14), s(14,8), s(8,11), s(11,10), s(10,7), s(7,6), s(6,5), s(5,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,4) then 2 else
  if d.edge = s(4,2) then 3 else
  if d.edge = s(2,12) then 19 else
  if d.edge = s(12,9) then 18 else
  if d.edge = s(9,13) then 17 else
  if d.edge = s(13,14) then 28 else
  if d.edge = s(14,8) then 27 else
  if d.edge = s(8,11) then 26 else
  if d.edge = s(11,10) then 13 else
  if d.edge = s(10,7) then 21 else
  if d.edge = s(7,6) then 7 else
  if d.edge = s(6,5) then 6 else
  5
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 4 by decide) (.cons (show redGraph.Adj 4 2 by decide) (.cons (show redGraph.Adj 2 12 by decide) (.cons (show redGraph.Adj 12 9 by decide) (.cons (show redGraph.Adj 9 13 by decide) (.cons (show redGraph.Adj 13 14 by decide) (.cons (show redGraph.Adj 14 8 by decide) (.cons (show redGraph.Adj 8 11 by decide) (.cons (show redGraph.Adj 11 10 by decide) (.cons (show redGraph.Adj 10 7 by decide) (.cons (show redGraph.Adj 7 6 by decide) (.cons (show redGraph.Adj 6 5 by decide) (.cons (show redGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,2), s(2,6), s(6,13), s(13,4), s(4,11), s(11,5), s(5,9), s(9,1), s(1,10), s(10,12), s(12,14), s(14,3), s(3,7), s(7,8), s(8,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,2) then 4 else
  if d.edge = s(2,6) then 15 else
  if d.edge = s(6,13) then 16 else
  if d.edge = s(13,4) then 29 else
  if d.edge = s(4,11) then 25 else
  if d.edge = s(11,5) then 12 else
  if d.edge = s(5,9) then 11 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,10) then 14 else
  if d.edge = s(10,12) then 22 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,3) then 24 else
  if d.edge = s(3,7) then 20 else
  if d.edge = s(7,8) then 8 else
  9
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 2 by decide) (.cons (show blueGraph.Adj 2 6 by decide) (.cons (show blueGraph.Adj 6 13 by decide) (.cons (show blueGraph.Adj 13 4 by decide) (.cons (show blueGraph.Adj 4 11 by decide) (.cons (show blueGraph.Adj 11 5 by decide) (.cons (show blueGraph.Adj 5 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 10 by decide) (.cons (show blueGraph.Adj 10 12 by decide) (.cons (show blueGraph.Adj 12 14 by decide) (.cons (show blueGraph.Adj 14 3 by decide) (.cons (show blueGraph.Adj 3 7 by decide) (.cons (show blueGraph.Adj 7 8 by decide) (.cons (show blueGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout7

namespace Layout8
def src : Fin 30 → Fin 15 := ![0,1,3,4,2,0,5,6,7,8,1,9,5,11,10,2,6,13,9,12,3,7,10,12,14,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,3,4,2,0,5,6,7,8,0,9,5,11,10,1,6,13,9,12,2,7,10,12,14,3,11,14,8,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,4), s(4,11), s(11,5), s(5,9), s(9,13), s(13,8), s(8,14), s(14,12), s(12,10), s(10,7), s(7,6), s(6,2), s(2,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,4) then 2 else
  if d.edge = s(4,11) then 25 else
  if d.edge = s(11,5) then 12 else
  if d.edge = s(5,9) then 11 else
  if d.edge = s(9,13) then 17 else
  if d.edge = s(13,8) then 28 else
  if d.edge = s(8,14) then 27 else
  if d.edge = s(14,12) then 23 else
  if d.edge = s(12,10) then 22 else
  if d.edge = s(10,7) then 21 else
  if d.edge = s(7,6) then 7 else
  if d.edge = s(6,2) then 15 else
  4
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 4 by decide) (.cons (show redGraph.Adj 4 11 by decide) (.cons (show redGraph.Adj 11 5 by decide) (.cons (show redGraph.Adj 5 9 by decide) (.cons (show redGraph.Adj 9 13 by decide) (.cons (show redGraph.Adj 13 8 by decide) (.cons (show redGraph.Adj 8 14 by decide) (.cons (show redGraph.Adj 14 12 by decide) (.cons (show redGraph.Adj 12 10 by decide) (.cons (show redGraph.Adj 10 7 by decide) (.cons (show redGraph.Adj 7 6 by decide) (.cons (show redGraph.Adj 6 2 by decide) (.cons (show redGraph.Adj 2 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,5), s(5,6), s(6,13), s(13,4), s(4,2), s(2,12), s(12,9), s(9,1), s(1,10), s(10,11), s(11,14), s(14,3), s(3,7), s(7,8), s(8,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,5) then 5 else
  if d.edge = s(5,6) then 6 else
  if d.edge = s(6,13) then 16 else
  if d.edge = s(13,4) then 29 else
  if d.edge = s(4,2) then 3 else
  if d.edge = s(2,12) then 19 else
  if d.edge = s(12,9) then 18 else
  if d.edge = s(9,1) then 10 else
  if d.edge = s(1,10) then 14 else
  if d.edge = s(10,11) then 13 else
  if d.edge = s(11,14) then 26 else
  if d.edge = s(14,3) then 24 else
  if d.edge = s(3,7) then 20 else
  if d.edge = s(7,8) then 8 else
  9
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 5 by decide) (.cons (show blueGraph.Adj 5 6 by decide) (.cons (show blueGraph.Adj 6 13 by decide) (.cons (show blueGraph.Adj 13 4 by decide) (.cons (show blueGraph.Adj 4 2 by decide) (.cons (show blueGraph.Adj 2 12 by decide) (.cons (show blueGraph.Adj 12 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 10 by decide) (.cons (show blueGraph.Adj 10 11 by decide) (.cons (show blueGraph.Adj 11 14 by decide) (.cons (show blueGraph.Adj 14 3 by decide) (.cons (show blueGraph.Adj 3 7 by decide) (.cons (show blueGraph.Adj 7 8 by decide) (.cons (show blueGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout8

namespace Layout9
def src : Fin 30 → Fin 15 := ![0,1,3,4,2,0,5,8,6,7,1,9,5,10,11,2,6,13,9,12,3,12,10,7,14,4,8,14,13,11]
def dst : Fin 30 → Fin 15 := ![1,3,4,2,0,5,8,6,7,0,9,5,10,11,1,6,13,9,12,2,12,10,7,14,3,8,14,13,11,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,3), s(3,4), s(4,8), s(8,14), s(14,13), s(13,11), s(11,10), s(10,7), s(7,6), s(6,2), s(2,12), s(12,9), s(9,5), s(5,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,3) then 1 else
  if d.edge = s(3,4) then 2 else
  if d.edge = s(4,8) then 25 else
  if d.edge = s(8,14) then 26 else
  if d.edge = s(14,13) then 27 else
  if d.edge = s(13,11) then 28 else
  if d.edge = s(11,10) then 13 else
  if d.edge = s(10,7) then 22 else
  if d.edge = s(7,6) then 8 else
  if d.edge = s(6,2) then 15 else
  if d.edge = s(2,12) then 19 else
  if d.edge = s(12,9) then 18 else
  if d.edge = s(9,5) then 11 else
  5
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 3 by decide) (.cons (show redGraph.Adj 3 4 by decide) (.cons (show redGraph.Adj 4 8 by decide) (.cons (show redGraph.Adj 8 14 by decide) (.cons (show redGraph.Adj 14 13 by decide) (.cons (show redGraph.Adj 13 11 by decide) (.cons (show redGraph.Adj 11 10 by decide) (.cons (show redGraph.Adj 10 7 by decide) (.cons (show redGraph.Adj 7 6 by decide) (.cons (show redGraph.Adj 6 2 by decide) (.cons (show redGraph.Adj 2 12 by decide) (.cons (show redGraph.Adj 12 9 by decide) (.cons (show redGraph.Adj 9 5 by decide) (.cons (show redGraph.Adj 5 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,2), s(2,4), s(4,11), s(11,1), s(1,9), s(9,13), s(13,6), s(6,8), s(8,5), s(5,10), s(10,12), s(12,3), s(3,14), s(14,7), s(7,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,2) then 4 else
  if d.edge = s(2,4) then 3 else
  if d.edge = s(4,11) then 29 else
  if d.edge = s(11,1) then 14 else
  if d.edge = s(1,9) then 10 else
  if d.edge = s(9,13) then 17 else
  if d.edge = s(13,6) then 16 else
  if d.edge = s(6,8) then 7 else
  if d.edge = s(8,5) then 6 else
  if d.edge = s(5,10) then 12 else
  if d.edge = s(10,12) then 21 else
  if d.edge = s(12,3) then 20 else
  if d.edge = s(3,14) then 24 else
  if d.edge = s(14,7) then 23 else
  9
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 2 by decide) (.cons (show blueGraph.Adj 2 4 by decide) (.cons (show blueGraph.Adj 4 11 by decide) (.cons (show blueGraph.Adj 11 1 by decide) (.cons (show blueGraph.Adj 1 9 by decide) (.cons (show blueGraph.Adj 9 13 by decide) (.cons (show blueGraph.Adj 13 6 by decide) (.cons (show blueGraph.Adj 6 8 by decide) (.cons (show blueGraph.Adj 8 5 by decide) (.cons (show blueGraph.Adj 5 10 by decide) (.cons (show blueGraph.Adj 10 12 by decide) (.cons (show blueGraph.Adj 12 3 by decide) (.cons (show blueGraph.Adj 3 14 by decide) (.cons (show blueGraph.Adj 14 7 by decide) (.cons (show blueGraph.Adj 7 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout9

namespace Layout10
def src : Fin 30 → Fin 15 := ![0,1,2,3,4,0,5,6,8,7,1,9,10,5,11,2,6,12,9,13,3,10,7,14,12,4,8,11,14,13]
def dst : Fin 30 → Fin 15 := ![1,2,3,4,0,5,6,8,7,0,9,10,5,11,1,6,12,9,13,2,10,7,14,12,3,8,11,14,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,2), s(2,3), s(3,12), s(12,6), s(6,5), s(5,11), s(11,14), s(14,13), s(13,9), s(9,10), s(10,7), s(7,8), s(8,4), s(4,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,2) then 1 else
  if d.edge = s(2,3) then 2 else
  if d.edge = s(3,12) then 24 else
  if d.edge = s(12,6) then 16 else
  if d.edge = s(6,5) then 6 else
  if d.edge = s(5,11) then 13 else
  if d.edge = s(11,14) then 27 else
  if d.edge = s(14,13) then 28 else
  if d.edge = s(13,9) then 18 else
  if d.edge = s(9,10) then 11 else
  if d.edge = s(10,7) then 21 else
  if d.edge = s(7,8) then 8 else
  if d.edge = s(8,4) then 25 else
  4
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 3 by decide) (.cons (show redGraph.Adj 3 12 by decide) (.cons (show redGraph.Adj 12 6 by decide) (.cons (show redGraph.Adj 6 5 by decide) (.cons (show redGraph.Adj 5 11 by decide) (.cons (show redGraph.Adj 11 14 by decide) (.cons (show redGraph.Adj 14 13 by decide) (.cons (show redGraph.Adj 13 9 by decide) (.cons (show redGraph.Adj 9 10 by decide) (.cons (show redGraph.Adj 10 7 by decide) (.cons (show redGraph.Adj 7 8 by decide) (.cons (show redGraph.Adj 8 4 by decide) (.cons (show redGraph.Adj 4 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,5), s(5,10), s(10,3), s(3,4), s(4,13), s(13,2), s(2,6), s(6,8), s(8,11), s(11,1), s(1,9), s(9,12), s(12,14), s(14,7), s(7,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,5) then 5 else
  if d.edge = s(5,10) then 12 else
  if d.edge = s(10,3) then 20 else
  if d.edge = s(3,4) then 3 else
  if d.edge = s(4,13) then 29 else
  if d.edge = s(13,2) then 19 else
  if d.edge = s(2,6) then 15 else
  if d.edge = s(6,8) then 7 else
  if d.edge = s(8,11) then 26 else
  if d.edge = s(11,1) then 14 else
  if d.edge = s(1,9) then 10 else
  if d.edge = s(9,12) then 17 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,7) then 22 else
  9
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 5 by decide) (.cons (show blueGraph.Adj 5 10 by decide) (.cons (show blueGraph.Adj 10 3 by decide) (.cons (show blueGraph.Adj 3 4 by decide) (.cons (show blueGraph.Adj 4 13 by decide) (.cons (show blueGraph.Adj 13 2 by decide) (.cons (show blueGraph.Adj 2 6 by decide) (.cons (show blueGraph.Adj 6 8 by decide) (.cons (show blueGraph.Adj 8 11 by decide) (.cons (show blueGraph.Adj 11 1 by decide) (.cons (show blueGraph.Adj 1 9 by decide) (.cons (show blueGraph.Adj 9 12 by decide) (.cons (show blueGraph.Adj 12 14 by decide) (.cons (show blueGraph.Adj 14 7 by decide) (.cons (show blueGraph.Adj 7 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout10

namespace Layout11
def src : Fin 30 → Fin 15 := ![0,1,2,3,4,0,7,6,5,8,1,9,10,5,11,2,6,12,9,13,3,10,7,14,12,4,11,14,8,13]
def dst : Fin 30 → Fin 15 := ![1,2,3,4,0,7,6,5,8,0,9,10,5,11,1,6,12,9,13,2,10,7,14,12,3,11,14,8,13,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,2), s(2,3), s(3,12), s(12,6), s(6,5), s(5,8), s(8,14), s(14,11), s(11,4), s(4,13), s(13,9), s(9,10), s(10,7), s(7,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,2) then 1 else
  if d.edge = s(2,3) then 2 else
  if d.edge = s(3,12) then 24 else
  if d.edge = s(12,6) then 16 else
  if d.edge = s(6,5) then 7 else
  if d.edge = s(5,8) then 8 else
  if d.edge = s(8,14) then 27 else
  if d.edge = s(14,11) then 26 else
  if d.edge = s(11,4) then 25 else
  if d.edge = s(4,13) then 29 else
  if d.edge = s(13,9) then 18 else
  if d.edge = s(9,10) then 11 else
  if d.edge = s(10,7) then 21 else
  5
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 3 by decide) (.cons (show redGraph.Adj 3 12 by decide) (.cons (show redGraph.Adj 12 6 by decide) (.cons (show redGraph.Adj 6 5 by decide) (.cons (show redGraph.Adj 5 8 by decide) (.cons (show redGraph.Adj 8 14 by decide) (.cons (show redGraph.Adj 14 11 by decide) (.cons (show redGraph.Adj 11 4 by decide) (.cons (show redGraph.Adj 4 13 by decide) (.cons (show redGraph.Adj 13 9 by decide) (.cons (show redGraph.Adj 9 10 by decide) (.cons (show redGraph.Adj 10 7 by decide) (.cons (show redGraph.Adj 7 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,4), s(4,3), s(3,10), s(10,5), s(5,11), s(11,1), s(1,9), s(9,12), s(12,14), s(14,7), s(7,6), s(6,2), s(2,13), s(13,8), s(8,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,4) then 4 else
  if d.edge = s(4,3) then 3 else
  if d.edge = s(3,10) then 20 else
  if d.edge = s(10,5) then 12 else
  if d.edge = s(5,11) then 13 else
  if d.edge = s(11,1) then 14 else
  if d.edge = s(1,9) then 10 else
  if d.edge = s(9,12) then 17 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,7) then 22 else
  if d.edge = s(7,6) then 6 else
  if d.edge = s(6,2) then 15 else
  if d.edge = s(2,13) then 19 else
  if d.edge = s(13,8) then 28 else
  9
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 4 by decide) (.cons (show blueGraph.Adj 4 3 by decide) (.cons (show blueGraph.Adj 3 10 by decide) (.cons (show blueGraph.Adj 10 5 by decide) (.cons (show blueGraph.Adj 5 11 by decide) (.cons (show blueGraph.Adj 11 1 by decide) (.cons (show blueGraph.Adj 1 9 by decide) (.cons (show blueGraph.Adj 9 12 by decide) (.cons (show blueGraph.Adj 12 14 by decide) (.cons (show blueGraph.Adj 14 7 by decide) (.cons (show blueGraph.Adj 7 6 by decide) (.cons (show blueGraph.Adj 6 2 by decide) (.cons (show blueGraph.Adj 2 13 by decide) (.cons (show blueGraph.Adj 13 8 by decide) (.cons (show blueGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout11

namespace Layout12
def src : Fin 30 → Fin 15 := ![0,1,2,4,3,0,7,6,5,8,1,5,11,10,9,2,6,12,9,13,3,10,7,14,12,4,8,14,13,11]
def dst : Fin 30 → Fin 15 := ![1,2,4,3,0,7,6,5,8,0,5,11,10,9,1,6,12,9,13,2,10,7,14,12,3,8,14,13,11,4]

def redEdges : Finset (Sym2 (Fin 15)) := {s(0,1), s(1,2), s(2,4), s(4,3), s(3,10), s(10,11), s(11,13), s(13,9), s(9,12), s(12,14), s(14,8), s(8,5), s(5,6), s(6,7), s(7,0)}
def redGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 30 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,2) then 1 else
  if d.edge = s(2,4) then 2 else
  if d.edge = s(4,3) then 3 else
  if d.edge = s(3,10) then 20 else
  if d.edge = s(10,11) then 12 else
  if d.edge = s(11,13) then 28 else
  if d.edge = s(13,9) then 18 else
  if d.edge = s(9,12) then 17 else
  if d.edge = s(12,14) then 23 else
  if d.edge = s(14,8) then 26 else
  if d.edge = s(8,5) then 8 else
  if d.edge = s(5,6) then 7 else
  if d.edge = s(6,7) then 6 else
  5
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 := .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 4 by decide) (.cons (show redGraph.Adj 4 3 by decide) (.cons (show redGraph.Adj 3 10 by decide) (.cons (show redGraph.Adj 10 11 by decide) (.cons (show redGraph.Adj 11 13 by decide) (.cons (show redGraph.Adj 13 9 by decide) (.cons (show redGraph.Adj 9 12 by decide) (.cons (show redGraph.Adj 12 14 by decide) (.cons (show redGraph.Adj 14 8 by decide) (.cons (show redGraph.Adj 8 5 by decide) (.cons (show redGraph.Adj 5 6 by decide) (.cons (show redGraph.Adj 6 7 by decide) (.cons (show redGraph.Adj 7 0 by decide) (.nil)))))))))))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 15)) := {s(0,3), s(3,12), s(12,6), s(6,2), s(2,13), s(13,14), s(14,7), s(7,10), s(10,9), s(9,1), s(1,5), s(5,11), s(11,4), s(4,8), s(8,0)}
def blueGraph : SimpleGraph (Fin 15) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 30 :=
  if d.edge = s(0,3) then 4 else
  if d.edge = s(3,12) then 24 else
  if d.edge = s(12,6) then 16 else
  if d.edge = s(6,2) then 15 else
  if d.edge = s(2,13) then 19 else
  if d.edge = s(13,14) then 27 else
  if d.edge = s(14,7) then 22 else
  if d.edge = s(7,10) then 21 else
  if d.edge = s(10,9) then 13 else
  if d.edge = s(9,1) then 14 else
  if d.edge = s(1,5) then 10 else
  if d.edge = s(5,11) then 11 else
  if d.edge = s(11,4) then 29 else
  if d.edge = s(4,8) then 25 else
  9
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 := .cons (show blueGraph.Adj 0 3 by decide) (.cons (show blueGraph.Adj 3 12 by decide) (.cons (show blueGraph.Adj 12 6 by decide) (.cons (show blueGraph.Adj 6 2 by decide) (.cons (show blueGraph.Adj 2 13 by decide) (.cons (show blueGraph.Adj 13 14 by decide) (.cons (show blueGraph.Adj 14 7 by decide) (.cons (show blueGraph.Adj 7 10 by decide) (.cons (show blueGraph.Adj 10 9 by decide) (.cons (show blueGraph.Adj 9 1 by decide) (.cons (show blueGraph.Adj 1 5 by decide) (.cons (show blueGraph.Adj 5 11 by decide) (.cons (show blueGraph.Adj 11 4 by decide) (.cons (show blueGraph.Adj 4 8 by decide) (.cons (show blueGraph.Adj 8 0 by decide) (.nil)))))))))))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 30) (Fin 15) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Layout12

end Erdos184Work.SixCycleCertificates
