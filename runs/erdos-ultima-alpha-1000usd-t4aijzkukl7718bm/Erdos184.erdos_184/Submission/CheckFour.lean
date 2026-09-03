import Submission.RigidityDegree

/-! Unrestricted segmentation of a cycle at four specified vertices.
Unlike the earlier alternating-contact lemma, no rigidity is assumed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
open RigidSwitching
set_option maxHeartbeats 2000000
variable {V : Type*} {G : SimpleGraph V}

lemma exists_pathParts_support {u v w : V} (p : G.Walk u v) (hp : p.IsPath)
    (hw : w ∈ p.support) :
    ∃ P : PathParts p w, ∀ z, (z ∈ P.first.support ∨ z ∈ P.last.support) ↔ z ∈ p.support := by
  let P : PathParts p w :=
    ⟨p.takeUntil w hw,p.dropUntil w hw,hp.takeUntil hw,hp.dropUntil hw,
      hp.isTrail.disjoint_edges_takeUntil_dropUntil hw,by
        intro e
        rw [← List.mem_append,← Walk.edges_append,Walk.take_spec]⟩
  refine ⟨P,?_⟩
  intro z
  change (z ∈ (p.takeUntil w hw).support ∨ z ∈ (p.dropUntil w hw).support) ↔ _
  rw [← Walk.mem_support_append_iff,Walk.take_spec]

structure PathThirds {u v : V} (p : G.Walk u v) (x y : V) where
  first : G.Walk u x
  middle : G.Walk x y
  last : G.Walk y v
  first_path : first.IsPath
  middle_path : middle.IsPath
  last_path : last.IsPath
  first_middle : first.edges.Disjoint middle.edges
  first_last : first.edges.Disjoint last.edges
  middle_last : middle.edges.Disjoint last.edges
  cover : ∀ e, (e ∈ first.edges ∨ e ∈ middle.edges ∨ e ∈ last.edges) ↔ e ∈ p.edges

namespace PathThirds
variable {u v x y : V} {p : G.Walk u v}
lemma first_edges_subset (Q : PathThirds p x y) : Q.first.edges ⊆ p.edges :=
  fun e he => (Q.cover e).mp (Or.inl he)
lemma middle_edges_subset (Q : PathThirds p x y) : Q.middle.edges ⊆ p.edges :=
  fun e he => (Q.cover e).mp (Or.inr (Or.inl he))
lemma last_edges_subset (Q : PathThirds p x y) : Q.last.edges ⊆ p.edges :=
  fun e he => (Q.cover e).mp (Or.inr (Or.inr he))
end PathThirds

lemma exists_pathThirds {u v x y : V} (p : G.Walk u v) (hp : p.IsPath)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    Nonempty (PathThirds p x y) ∨ Nonempty (PathThirds p y x) := by
  obtain ⟨P,hP⟩ := exists_pathParts_support p hp hx
  rcases (hP y).mpr hy with hy | hy
  · obtain ⟨Q⟩ := exists_pathParts P.first P.first_path hy
    right
    refine ⟨⟨Q.first,Q.last,P.last,Q.first_path,Q.last_path,P.last_path,
      Q.edges_disjoint,
      disjoint_mono P.edges_disjoint Q.first_edges_subset (List.Subset.refl _),
      disjoint_mono P.edges_disjoint Q.last_edges_subset (List.Subset.refl _),?_⟩⟩
    intro e
    rw [← P.edges_cover e,← Q.edges_cover e]
    tauto
  · obtain ⟨Q⟩ := exists_pathParts P.last P.last_path hy
    left
    refine ⟨⟨P.first,Q.first,Q.last,P.first_path,Q.first_path,Q.last_path,
      disjoint_mono P.edges_disjoint (List.Subset.refl _) Q.first_edges_subset,
      disjoint_mono P.edges_disjoint (List.Subset.refl _) Q.last_edges_subset,
      Q.edges_disjoint,?_⟩⟩
    intro e
    rw [← P.edges_cover e,← Q.edges_cover e]

lemma four_segments_of_thirds {u v x y : V} {c : G.Walk u u}
    (P : CyclePaths c v) (Q : PathThirds P.left x y) :
    Nonempty (Segmentation c ![u,v,y,x] src4 dst4) := by
#check exists_pathThirds
#print exists_pathThirds
end Erdos184Work.CycleSegments
