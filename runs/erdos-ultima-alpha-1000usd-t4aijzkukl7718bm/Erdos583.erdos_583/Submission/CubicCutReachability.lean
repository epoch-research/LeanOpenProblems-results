import Submission.ShortTriangleEndpointTransfer

/-! Reachability on the two sides of a deleted edge, and contraction of a cubic triangle. -/
namespace Erdos583CubicCutReachabilityDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma deleted_edge_two_sides {V : Type*} {G : SimpleGraph V} (hG : SupportConnected G)
    {a b : V} (hab : G.Adj a b) {v : V} (hv : v ∈ G.support) :
    (G.deleteEdges {s(a,b)}).Reachable a v ∨ (G.deleteEdges {s(a,b)}).Reachable b v := by
  let F := G.deleteEdges {s(a,b)}
  let S : Set V := {z | F.Reachable a z ∨ F.Reachable b z}
  have hh : G.support ⊆ S := by
    apply hG.support_subset_of_closed (show a ∈ G.support from ⟨b,hab⟩) (show a ∈ S from Or.inl .rfl)
    intro u hu z huz
    by_cases he : s(u,z)=s(a,b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr .rfl
      · exact Or.inl .rfl
    · have hF : F.Reachable u z := (show F.Adj u z from deleteEdges_adj.mpr ⟨huz,he⟩).reachable
      exact hu.elim (fun h ↦ Or.inl (h.trans hF)) (fun h ↦ Or.inr (h.trans hF))
  exact hh hv

lemma cubic_cut_walk_separation {V : Type*} {G : SimpleGraph V} {r x y a b u v : V}
    (hrx : r ≠ x) (hry : r ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hra : (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r a)
    (hnrb : ¬(puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r b)
    (P : G.Walk u v) (hnab : s(a,b) ∉ P.edges) (hnyb : s(y,b) ∉ P.edges)
    (hrP : r ∈ P.support) (hbP : b ∈ P.support) : False := by
  classical
  let S : Set V := {x,y}
  let K := puncture (G.deleteEdges {s(a,b)}) S
  let J := G.deleteEdges ({s(a,b),s(y,b)} : Set (Sym2 V))
  let f (z : V) := if z ∈ S then r else z
  have hboundary {t z : V} (ht : t ∈ S) (hz : z ∉ S) (htz : J.Adj t z) : K.Reachable r z := by
    have hh := deleteEdges_adj.mp htz
    rcases ht with rfl | rfl
    · rcases hNx z hh.1 with rfl | rfl | rfl
      · exact .rfl
      · exact (hz (Or.inr rfl)).elim
      · exact hra
    · rcases hNy z hh.1 with rfl | rfl | rfl
      · exact .rfl
      · exact (hz (Or.inl rfl)).elim
      · exact (hh.2 (Or.inr rfl)).elim
  have hedge (s t : V) (hst : J.Adj s t) : K.Reachable (f s) (f t) := by
    by_cases hs : s ∈ S <;> by_cases ht : t ∈ S
    · simp only [f,if_pos hs,if_pos ht]; exact .rfl
    · simp only [f,if_pos hs,if_neg ht]; exact hboundary hs ht hst
    · simp only [f,if_neg hs,if_pos ht]; exact (hboundary ht hs hst.symm).symm
    · simp only [f,if_neg hs,if_neg ht]
      exact (show K.Adj s t from ⟨deleteEdges_adj.mpr
        ⟨(deleteEdges_adj.mp hst).1,fun he ↦ (deleteEdges_adj.mp hst).2 (Or.inl he)⟩,hs,ht⟩).reachable
  have htransfer : ∀ e ∈ P.edges, e ∈ J.edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    exact ⟨P.edges_subset_edgeSet he,fun hh ↦ hh.elim (fun hh ↦ hnab (hh ▸ he)) (fun hh ↦ hnyb (hh ▸ he))⟩
  let Q := P.transfer J htransfer
  have hrQ : r ∈ Q.support := by simpa only [Q,Walk.support_transfer] using hrP
  have hbQ : b ∈ Q.support := by simpa only [Q,Walk.support_transfer] using hbP
  have hrr : J.Reachable r b := (Q.takeUntil r hrQ).reachable.symm.trans (Q.takeUntil b hbQ).reachable
  apply hnrb
  simpa only [f,S,Set.mem_insert_iff,Set.mem_singleton_iff,hrx,hry,hbx,hby,or_self,↓reduceIte]
    using reachable_map_to_reachable f hedge hrr

end Erdos583CubicCutReachabilityDevelopment
