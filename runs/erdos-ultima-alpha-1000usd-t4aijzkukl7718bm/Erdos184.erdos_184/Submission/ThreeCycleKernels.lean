import Submission.PathSubstitution

/-! Two-cycle decompositions of the four alternating three-cycle junction kernels,
including arbitrary internally disjoint path replacements. -/

open SimpleGraph
namespace Erdos184Work.ThreeCycleKernels
open PathSubstitution
namespace DoubleTriangle
def src : Fin 6 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 2
def dst : Fin 6 → Fin 3
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | 4 => 2
  | 5 => 1

def redEdges : Finset (Sym2 (Fin 3)) :=
  {s(0,1), s(1,2), s(2,0)}
def redGraph : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 6 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,2) then 4 else 3
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 0 by decide) (.nil)))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 3)) :=
  {s(0,1), s(1,2), s(2,0)}
def blueGraph : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 6 :=
  if d.edge = s(0,1) then 1 else
  if d.edge = s(1,2) then 5 else 2
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 1 by decide) (.cons (show blueGraph.Adj 1 2 by decide) (.cons (show blueGraph.Adj 2 0 by decide) (.nil)))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 6) (Fin 3) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end DoubleTriangle

namespace MatchedFour
def src : Fin 8 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 3
def dst : Fin 8 → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 3
  | 5 => 0
  | 6 => 3
  | 7 => 2

def redEdges : Finset (Sym2 (Fin 4)) :=
  {s(0,1), s(1,2), s(2,3), s(3,0)}
def redGraph : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 8 :=
  if d.edge = s(0,1) then 0 else
  if d.edge = s(1,2) then 1 else
  if d.edge = s(2,3) then 6 else 5
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 3 by decide) (.cons (show redGraph.Adj 3 0 by decide) (.nil))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 4)) :=
  {s(0,1), s(1,3), s(3,2), s(2,0)}
def blueGraph : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 8 :=
  if d.edge = s(0,1) then 3 else
  if d.edge = s(1,3) then 4 else
  if d.edge = s(3,2) then 7 else 2
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 1 by decide) (.cons (show blueGraph.Adj 1 3 by decide) (.cons (show blueGraph.Adj 3 2 by decide) (.cons (show blueGraph.Adj 2 0 by decide) (.nil))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 8) (Fin 4) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end MatchedFour

namespace CompleteFive
def src : Fin 10 → Fin 5
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 4
  | 7 => 2
  | 8 => 3
  | 9 => 4
def dst : Fin 10 → Fin 5
  | 0 => 2
  | 1 => 1
  | 2 => 3
  | 3 => 0
  | 4 => 1
  | 5 => 4
  | 6 => 0
  | 7 => 3
  | 8 => 4
  | 9 => 2

def redEdges : Finset (Sym2 (Fin 5)) :=
  {s(0,1), s(1,2), s(2,3), s(3,4), s(4,0)}
def redGraph : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 10 :=
  if d.edge = s(0,1) then 4 else
  if d.edge = s(1,2) then 1 else
  if d.edge = s(2,3) then 7 else
  if d.edge = s(3,4) then 8 else 6
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 1 by decide) (.cons (show redGraph.Adj 1 2 by decide) (.cons (show redGraph.Adj 2 3 by decide) (.cons (show redGraph.Adj 3 4 by decide) (.cons (show redGraph.Adj 4 0 by decide) (.nil)))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 5)) :=
  {s(0,2), s(2,4), s(4,1), s(1,3), s(3,0)}
def blueGraph : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 10 :=
  if d.edge = s(0,2) then 0 else
  if d.edge = s(2,4) then 9 else
  if d.edge = s(4,1) then 5 else
  if d.edge = s(1,3) then 2 else 3
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 2 by decide) (.cons (show blueGraph.Adj 2 4 by decide) (.cons (show blueGraph.Adj 4 1 by decide) (.cons (show blueGraph.Adj 1 3 by decide) (.cons (show blueGraph.Adj 3 0 by decide) (.nil)))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 10) (Fin 5) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end CompleteFive

namespace Octahedron
def src : Fin 12 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 0
  | 5 => 4
  | 6 => 1
  | 7 => 5
  | 8 => 2
  | 9 => 4
  | 10 => 3
  | 11 => 5
def dst : Fin 12 → Fin 6
  | 0 => 2
  | 1 => 1
  | 2 => 3
  | 3 => 0
  | 4 => 4
  | 5 => 1
  | 6 => 5
  | 7 => 0
  | 8 => 4
  | 9 => 3
  | 10 => 5
  | 11 => 2

def redEdges : Finset (Sym2 (Fin 6)) :=
  {s(0,2), s(2,1), s(1,4), s(4,3), s(3,5), s(5,0)}
def redGraph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet redEdges
instance : DecidableRel redGraph.Adj := by unfold redGraph; infer_instance
def redRoute (d : redGraph.Dart) : Fin 12 :=
  if d.edge = s(0,2) then 0 else
  if d.edge = s(2,1) then 1 else
  if d.edge = s(1,4) then 5 else
  if d.edge = s(4,3) then 9 else
  if d.edge = s(3,5) then 10 else 7
lemma redEnds : ∀ d, s(src (redRoute d),dst (redRoute d)) = d.edge := by decide
def redWalk : redGraph.Walk 0 0 :=
  .cons (show redGraph.Adj 0 2 by decide) (.cons (show redGraph.Adj 2 1 by decide) (.cons (show redGraph.Adj 1 4 by decide) (.cons (show redGraph.Adj 4 3 by decide) (.cons (show redGraph.Adj 3 5 by decide) (.cons (show redGraph.Adj 5 0 by decide) (.nil))))))
lemma redCycle : redWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

def blueEdges : Finset (Sym2 (Fin 6)) :=
  {s(0,3), s(3,1), s(1,5), s(5,2), s(2,4), s(4,0)}
def blueGraph : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet blueEdges
instance : DecidableRel blueGraph.Adj := by unfold blueGraph; infer_instance
def blueRoute (d : blueGraph.Dart) : Fin 12 :=
  if d.edge = s(0,3) then 3 else
  if d.edge = s(3,1) then 2 else
  if d.edge = s(1,5) then 6 else
  if d.edge = s(5,2) then 11 else
  if d.edge = s(2,4) then 8 else 4
lemma blueEnds : ∀ d, s(src (blueRoute d),dst (blueRoute d)) = d.edge := by decide
def blueWalk : blueGraph.Walk 0 0 :=
  .cons (show blueGraph.Adj 0 3 by decide) (.cons (show blueGraph.Adj 3 1 by decide) (.cons (show blueGraph.Adj 1 5 by decide) (.cons (show blueGraph.Adj 5 2 by decide) (.cons (show blueGraph.Adj 2 4 by decide) (.cons (show blueGraph.Adj 4 0 by decide) (.nil))))))
lemma blueCycle : blueWalk.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  decide

lemma routes_disjoint : (redWalk.darts.map redRoute).Disjoint (blueWalk.darts.map blueRoute) := by
  apply List.disjoint_toFinset_iff_disjoint.mp
  decide
lemma routes_cover : ∀ j, j ∈ redWalk.darts.map redRoute ∨ j ∈ blueWalk.darts.map blueRoute := by decide

lemma subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (F : Family (Fin 12) (Fin 6) G) (hs : F.src = src) (ht : F.dst = dst)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  apply F.number_le_two_lifted_cycles redGraph blueGraph redRoute blueRoute
    (fun d => by rw [hs,ht]; exact redEnds d)
    (fun d => by rw [hs,ht]; exact blueEnds d)
    redWalk blueWalk redCycle blueCycle routes_disjoint routes_cover hcover

#print axioms subdivision_number_le_two
end Octahedron

end Erdos184Work.ThreeCycleKernels
