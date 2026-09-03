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
  let paths : ∀ i : Fin 4, G.Walk (![u,v,y,x] (src4 i)) (![u,v,y,x] (dst4 i)) :=
    Fin.cases P.right (Fin.cases Q.last.reverse (Fin.cases Q.middle.reverse
      (Fin.cases Q.first.reverse (fun i => Fin.elim0 i))))
  have h01 := disjoint_mono P.edges_disjoint.symm (List.Subset.refl _) Q.last_edges_subset
  have h02 := disjoint_mono P.edges_disjoint.symm (List.Subset.refl _) Q.middle_edges_subset
  have h03 := disjoint_mono P.edges_disjoint.symm (List.Subset.refl _) Q.first_edges_subset
  have h12 := Q.middle_last.symm
  have h13 := Q.first_last.symm
  have h23 := Q.first_middle.symm
  refine ⟨⟨paths,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact P.right_path
    · exact Q.last_path.reverse
    · exact Q.middle_path.reverse
    · exact Q.first_path.reverse
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (P.right).edges.Disjoint (Q.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01
    · change (P.right).edges.Disjoint (Q.middle.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02
    · change (P.right).edges.Disjoint (Q.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h03
    · change (Q.last.reverse).edges.Disjoint (P.right).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01.symm
    · exact (hij rfl).elim
    · change (Q.last.reverse).edges.Disjoint (Q.middle.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12
    · change (Q.last.reverse).edges.Disjoint (Q.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h13
    · change (Q.middle.reverse).edges.Disjoint (P.right).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02.symm
    · change (Q.middle.reverse).edges.Disjoint (Q.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12.symm
    · exact (hij rfl).elim
    · change (Q.middle.reverse).edges.Disjoint (Q.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h23
    · change (Q.first.reverse).edges.Disjoint (P.right).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h03.symm
    · change (Q.first.reverse).edges.Disjoint (Q.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h13.symm
    · change (Q.first.reverse).edges.Disjoint (Q.middle.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h23.symm
    · exact (hij rfl).elim
  · intro e
    rw [Fin.exists_fin_succ,Fin.exists_fin_succ,Fin.exists_fin_two]
    change e ∈ c.edges ↔ e ∈ P.right.edges ∨ e ∈ Q.last.reverse.edges ∨
      e ∈ Q.middle.reverse.edges ∨ e ∈ Q.first.reverse.edges
    simp only [Walk.edges_reverse,List.mem_reverse]
    rw [← P.edges_cover e,← Q.cover e]
    tauto

/-- The three orders up to reversal, with the first vertex fixed. -/
def fourOrder (u v x y : V) : Fin 3 → Fin 4 → V :=
  ![![u,v,x,y],![u,v,y,x],![u,x,v,y]]

lemma four_segments_orders {u v x y : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (hx : x ∈ c.support) (hy : y ∈ c.support) (huv : u ≠ v) :
    ∃ k : Fin 3, Nonempty (Segmentation c (fourOrder u v x y k) src4 dst4) := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hv huv
  obtain ⟨P,hxP⟩ := P.exists_left_through hx
  by_cases hyR : y ∈ P.right.support
  · exact ⟨2,four_segments_of_paths P hxP hyR⟩
  · have hyL : y ∈ P.left.support := ((P.support_cover y).mpr hy).resolve_right hyR
    rcases exists_pathThirds P.left P.left_path hxP hyL with h | h
    · obtain ⟨Q⟩ := h
      exact ⟨1,four_segments_of_thirds P Q⟩
    · obtain ⟨Q⟩ := h
      exact ⟨0,four_segments_of_thirds P Q⟩

lemma four_segments_orders_any {a u v x y : V} (c : G.Walk a a) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (hx : x ∈ c.support)
    (hy : y ∈ c.support) (huv : u ≠ v) :
    ∃ k : Fin 3, Nonempty (Segmentation c (fourOrder u v x y k) src4 dst4) := by
  obtain ⟨k,⟨S⟩⟩ := four_segments_orders (c.rotate hu) (hc.rotate hu)
    ((c.mem_support_rotate_iff hu).mpr hv) ((c.mem_support_rotate_iff hu).mpr hx)
    ((c.mem_support_rotate_iff hu).mpr hy) huv
  exact ⟨k,⟨S.transfer (fun e => (c.rotate_edges hu).mem_iff)⟩⟩

#print axioms four_segments_orders_any
end Erdos184Work.CycleSegments
