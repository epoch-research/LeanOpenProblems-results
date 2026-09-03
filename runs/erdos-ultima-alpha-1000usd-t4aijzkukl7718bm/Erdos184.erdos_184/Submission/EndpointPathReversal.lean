import Submission.EndpointPathMaximality

/-! Reorientation and selection of endpoint paths without changing the packing. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 400000
variable {V : Type*} {G : SimpleGraph V}

def Piece.reverse (p : Piece G) : Piece G :=
  ⟨p.dst,p.src,p.walk.reverse,p.isPath.reverse,p.ne.symm⟩

lemma Maximal.rearrange {L M : List (Piece G)} (hL : Maximal L)
    (he : (edgeList M).Perm (edgeList L))
    (hv : (endpoints M).Perm (endpoints L)) : Maximal M := by
  refine ⟨⟨he.nodup_iff.mpr hL.1.1,hv.nodup_iff.mpr hL.1.2.1,?_⟩,?_⟩
  · intro v
    exact hv.mem_iff.mpr (hL.1.2.2 v)
  · intro N hN
    rw [he.length_eq]
    exact hL.2 N hN

lemma reverse_first_edge_perm (p : Piece G) (L : List (Piece G)) :
    (edgeList (p.reverse :: L)).Perm (edgeList (p :: L)) := by
  apply List.perm_iff_count.mpr
  intro e
  simp [edgeList_cons,Piece.reverse]

lemma reverse_first_end_perm (p : Piece G) (L : List (Piece G)) :
    (endpoints (p.reverse :: L)).Perm (endpoints (p :: L)) := by
  apply List.perm_iff_count.mpr
  intro v
  simp only [endpoints_cons,Piece.reverse,List.count_cons]
  omega

lemma Maximal.reverse_first {p : Piece G} {L : List (Piece G)}
    (hL : Maximal (p :: L)) : Maximal (p.reverse :: L) :=
  hL.rearrange (reverse_first_edge_perm p L) (reverse_first_end_perm p L)

lemma reverse_second_edge_perm (p q : Piece G) (L : List (Piece G)) :
    (edgeList (p :: q.reverse :: L)).Perm (edgeList (p :: q :: L)) := by
  exact (reverse_first_edge_perm q L).append_left p.walk.edges

lemma Maximal.reverse_second {p q : Piece G} {L : List (Piece G)}
    (hL : Maximal (p :: q :: L)) : Maximal (p :: q.reverse :: L) := by
  apply hL.rearrange (reverse_second_edge_perm p q L)
  exact (reverse_first_end_perm q L).append_left [p.src,p.dst]

lemma exists_terminal_head {L : List (Piece G)} (hL : Maximal L) (v : V) :
    ∃ (p : Piece G) (M : List (Piece G)),
      Maximal (p :: M) ∧ p.dst = v ∧ (edgeList (p :: M)).Perm (edgeList L) := by
  obtain ⟨p,hp,hv⟩ := List.mem_flatMap.mp (hL.1.2.2 v)
  have hperm := List.perm_cons_erase hp
  have hM := hL.perm hperm
  have he := (edgeList_perm hperm).symm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv | hv
  · exact ⟨p.reverse,L.erase p,hM.reverse_first,hv.symm,
      (reverse_first_edge_perm p _).trans he⟩
  · exact ⟨p,L.erase p,hM,hv.symm,he⟩

lemma exists_initial_second {p : Piece G} {L : List (Piece G)}
    (hL : Maximal (p :: L)) (v : V) (ha : v ≠ p.src) (hb : v ≠ p.dst) :
    ∃ (q : Piece G) (M : List (Piece G)),
      Maximal (p :: q :: M) ∧ q.src = v ∧
      (edgeList (p :: q :: M)).Perm (edgeList (p :: L)) := by
  have hv : v ∈ endpoints L := by
    have hh := hL.1.2.2 v
    simpa only [endpoints_cons,List.mem_cons,ha,hb,false_or] using hh
  obtain ⟨q,hq,hv⟩ := List.mem_flatMap.mp hv
  have hperm := (List.perm_cons_erase hq).cons p
  have hM := hL.perm hperm
  have he := (edgeList_perm hperm).symm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv | hv
  · exact ⟨q,L.erase q,hM,hv.symm,he⟩
  · exact ⟨q.reverse,L.erase q,hM.reverse_second,hv.symm,
      (reverse_second_edge_perm p q _).trans he⟩

lemma Admissible.second_ne_first {p q : Piece G} {L : List (Piece G)}
    (hL : Admissible (p :: q :: L)) : q ≠ p := by
  intro h
  subst q
  have hn := hL.2.1
  simp only [endpoints_cons,List.nodup_cons,List.mem_cons] at hn
  exact hn.1 (by simp)

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.exists_terminal_head
#print axioms Erdos184Work.OddPaths.exists_initial_second
