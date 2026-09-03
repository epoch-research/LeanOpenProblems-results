import Submission.OccurrenceFanRotation
import Submission.FanCycleAbsorption

/-! A single unused edge either moves an endpoint defect or closes it. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.OccurrenceFan
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma extend_piece (p : Piece G) {v t : V} (ht : t = p.src ∨ t = p.dst)
    (hvt : G.Adj v t) (hv : v ∉ p.walk.support) :
    ∃ q : Piece G, q.walk.edges.Perm (p.walk.edges ++ [s(v,t)]) ∧
      [q.src,q.dst,t].Perm [p.src,p.dst,v] := by
  obtain ⟨b,P,hP,hPs,hPe,hPv⟩ := p.starting_at ht
  have hvP : v ∉ P.support := fun h => hv (hPs.mem_iff.mp h)
  have hvb : v ≠ b := fun h => hvP (h.symm ▸ P.end_mem_support)
  let q : Piece G := ⟨v,b,Walk.cons hvt P,hP.cons hvP,hvb⟩
  refine ⟨q,?_,?_⟩
  · apply List.perm_iff_count.mpr
    intro e
    have he := hPe.count_eq e
    simp only [q,Walk.edges_cons,List.count_cons,List.count_append,List.count_nil]
    omega
  · apply List.perm_iff_count.mpr
    intro a
    have he := hPv.count_eq a
    simp only [q,List.count_cons,List.count_nil] at he ⊢
    omega

lemma extend_family {M : List (Piece G)} {p : Piece G} (hp : p ∈ M)
    {v t : V} (ht : t = p.src ∨ t = p.dst) (hvt : G.Adj v t)
    (hv : v ∉ p.walk.support) :
    ∃ N : List (Piece G), (edgeList N).Perm (edgeList M ++ [s(v,t)]) ∧
      (endpoints N ++ [t]).Perm (endpoints M ++ [v]) := by
  obtain ⟨q,hqe,hqv⟩ := extend_piece p ht hvt hv
  let N := q :: M.erase p
  have he := edgeList_perm (List.perm_cons_erase hp)
  have hv' := endpoints_perm (List.perm_cons_erase hp)
  refine ⟨N,?_,?_⟩
  · apply List.perm_iff_count.mpr
    intro e
    have he₁ := hqe.count_eq e
    have he₂ := he.count_eq e
    simp only [N,edgeList_cons,List.count_append,List.count_cons,List.count_nil] at he₁ he₂ ⊢
    omega
  · apply List.perm_iff_count.mpr
    intro a
    have he₁ := hqv.count_eq a
    have he₂ := hv'.count_eq a
    simp only [N,endpoints_cons,List.count_append,List.count_cons,List.count_nil] at he₁ he₂ ⊢
    omega

lemma owner_avoids {L : List (Piece G)} {v t : V}
    (ht : t ∉ touchingEndpoints L v) (hp : t ∈ endpoints L) :
    ∃ p ∈ L, (t = p.src ∨ t = p.dst) ∧ v ∉ p.walk.support := by
  obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp hp
  refine ⟨p,hp,by simpa only [List.mem_cons,List.not_mem_nil,or_false] using he,?_⟩
  intro hv
  apply ht
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
    ⟨p,mem_touchingPaths.mpr ⟨hp,hv⟩,he⟩)

/-- The first alternative covers one more edge. The second preserves the
number of covered edges and transfers the defect to a previously absent endpoint. -/
lemma edge_step {L : List (Piece G)} (hn : (edgeList L).Nodup) {v a : V}
    (ha : (G \ coveredGraph L).Adj v a) :
    (∃ N : List (Piece G), (edgeList N).Nodup ∧
      (edgeList N).Perm (edgeList L ++ [s(v,a)]) ∧
      (endpoints N ++ [a]).Perm (endpoints L ++ [v])) ∨
    (∃ (t : V) (N : List (Piece G)), t ∉ endpoints L ∧ G.Adj v t ∧
      (edgeList N).Nodup ∧ (edgeList N).length = (edgeList L).length ∧
      (endpoints N ++ [a]).Perm (endpoints L ++ [t])) := by
  obtain ⟨t,M,hvt,ht,hmn,hme,hmv,hkeep⟩ := rotate_endpoint_fan hn ha
  by_cases hp : t ∈ endpoints L
  · obtain ⟨p,hp,hep,hvp⟩ := owner_avoids ht hp
    obtain ⟨N,hne,hnv⟩ := extend_family (hkeep p hp hvp) hep hvt hvp
    have he := hne.trans hme
    refine Or.inl ⟨N,hne.nodup_iff.mpr hmn,he,?_⟩
    apply List.perm_iff_count.mpr
    intro x
    have h₁ := hmv.count_eq x
    have h₂ := hnv.count_eq x
    simp only [List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega
  · refine Or.inr ⟨t,M,hp,hvt,hmn.of_append_left,?_,hmv⟩
    have hl := hme.length_eq
    simpa only [List.length_append,List.length_singleton,Nat.add_left_inj] using hl

end Erdos184Work.OddPaths.OccurrenceFan
#print axioms Erdos184Work.OddPaths.OccurrenceFan.edge_step
