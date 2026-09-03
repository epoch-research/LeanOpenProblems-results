import Submission.EdgeHull

/-! Parity certificates under neighborhood transfer.
No assertion that all minimal graphs possess such a certificate is made. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Compression
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {u v w : V}
set_option maxHeartbeats 2000000

noncomputable def privateNeighbors (G : SimpleGraph V) (u v : V) : Finset V :=
  (G.neighborFinset v \ G.neighborFinset u).erase u

lemma mem_privateNeighbors :
    w ∈ privateNeighbors G u v ↔ w ≠ u ∧ G.Adj v w ∧ ¬ G.Adj u w := by
  simp [privateNeighbors]

lemma privateNeighbors_subset : privateNeighbors G u v ⊆ G.neighborFinset v := by
  intro w hw
  exact (G.mem_neighborFinset _ _).mpr ((mem_privateNeighbors.mp hw).2.1)

lemma not_mem_private_left : u ∉ privateNeighbors G u v := by simp [mem_privateNeighbors]
lemma not_mem_private_right : v ∉ privateNeighbors G u v := by simp [mem_privateNeighbors]

lemma transfer_neighbors_left (huv : u ≠ v) :
    (transfer G u v).neighborFinset u = G.neighborFinset u ∪ privateNeighbors G u v := by
  ext w
  by_cases hwu : w = u
  · subst w
    simp [mem_privateNeighbors]
  by_cases hwv : w = v
  · subst w
    simp [mem_privateNeighbors,transfer_adj_pair]
  simp only [Finset.mem_union,SimpleGraph.mem_neighborFinset,mem_privateNeighbors,
    transfer_adj_left G huv hwu hwv,hwu,true_and]
  tauto

lemma transfer_neighbors_right (huv : u ≠ v) :
    (transfer G u v).neighborFinset v = G.neighborFinset v \ privateNeighbors G u v := by
  ext w
  by_cases hwu : w = u
  · subst w
    simp only [Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,not_mem_private_left,
      not_false_eq_true,and_true]
    simpa only [SimpleGraph.adj_comm] using transfer_adj_pair G u v
  by_cases hwv : w = v
  · subst w
    simp
  simp only [Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,mem_privateNeighbors,
    transfer_adj_right G huv hwu hwv,hwu,true_and]
  tauto

lemma transfer_neighbors_other (hwu : w ≠ u) (hwv : w ≠ v) :
    (transfer G u v).neighborFinset w =
      if w ∈ privateNeighbors G u v then insert u ((G.neighborFinset w).erase v)
      else G.neighborFinset w := by
  by_cases huv : u = v
  · subst v
    have hn : w ∉ privateNeighbors G u u := by simp [mem_privateNeighbors]
    rw [if_neg hn]
    ext x
    simp only [SimpleGraph.mem_neighborFinset]
    rw [transfer_self]
  ext x
  by_cases hp : w ∈ privateNeighbors G u v
  · rw [if_pos hp]
    obtain ⟨_,hvw,huw⟩ := mem_privateNeighbors.mp hp
    by_cases hxu : x = u
    · subst x
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert_self,iff_true]
      exact ((transfer_adj_left G huv hwu hwv).mpr (Or.inr hvw)).symm
    by_cases hxv : x = v
    · subst x
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_erase,
        ne_eq,not_true_eq_false,false_and,or_false]
      constructor
      · intro hh
        exact (huw ((transfer_adj_right G huv hwu hwv).mp hh.symm).2).elim
      · intro hh
        exact (huv hh.symm).elim
    simp only [Finset.mem_insert,Finset.mem_erase,hxu,hxv,false_or,not_false_eq_true,
      true_and,SimpleGraph.mem_neighborFinset]
    constructor
    · intro hh
      exact ⟨hxv,(transfer_adj_away G hwu hwv hxu hxv).mp hh⟩
    · intro hh
      exact (transfer_adj_away G hwu hwv hxu hxv).mpr hh.2
  · rw [if_neg hp]
    have hnp : ¬ (G.Adj v w ∧ ¬ G.Adj u w) := by
      intro hh
      exact hp (mem_privateNeighbors.mpr ⟨hwu,hh⟩)
    by_cases hxu : x = u
    · subst x
      simp only [SimpleGraph.mem_neighborFinset]
      rw [SimpleGraph.adj_comm,transfer_adj_left G huv hwu hwv]
      rw [G.adj_comm]
      tauto
    by_cases hxv : x = v
    · subst x
      simp only [SimpleGraph.mem_neighborFinset]
      rw [SimpleGraph.adj_comm,transfer_adj_right G huv hwu hwv]
      rw [G.adj_comm]
      tauto
    simp only [SimpleGraph.mem_neighborFinset]
    exact transfer_adj_away G hwu hwv hxu hxv

lemma transfer_degree_left (huv : u ≠ v) :
    (transfer G u v).degree u = G.degree u + (privateNeighbors G u v).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,transfer_neighbors_left huv,
    Finset.card_union_of_disjoint]
  · rw [SimpleGraph.card_neighborFinset_eq_degree]
  · apply Finset.disjoint_left.mpr
    intro w hw hp
    exact (mem_privateNeighbors.mp hp).2.2 ((G.mem_neighborFinset _ _).mp hw)

lemma transfer_degree_right (huv : u ≠ v) :
    (transfer G u v).degree v + (privateNeighbors G u v).card = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,transfer_neighbors_right huv]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_sdiff_add_card_eq_card (privateNeighbors_subset (G := G) (u := u) (v := v))

lemma transfer_degree_other (hwu : w ≠ u) (hwv : w ≠ v) :
    (transfer G u v).degree w = G.degree w := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,transfer_neighbors_other hwu hwv]
  split_ifs with hp
  · obtain ⟨_,hvw,huw⟩ := mem_privateNeighbors.mp hp
    rw [Finset.card_insert_of_notMem,Finset.card_erase_of_mem]
    · have hpos : 0 < (G.neighborFinset w).card :=
        Finset.card_pos.mpr ⟨v,(G.mem_neighborFinset _ _).mpr hvw.symm⟩
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      omega
    · exact (G.mem_neighborFinset _ _).mpr hvw.symm
    · intro hu
      exact huw ((G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hu).2).symm
  · rw [SimpleGraph.card_neighborFinset_eq_degree]

lemma delete_edge_neighbors_left :
    (G.deleteEdges {s(u,v)}).neighborFinset u = (G.neighborFinset u).erase v := by
  ext x
  simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.deleteEdges_adj,
    Set.mem_singleton_iff,Sym2.eq_iff,Finset.mem_erase]
  constructor
  · rintro ⟨h,hne⟩
    exact ⟨fun hx => hne (Or.inl ⟨True.intro,hx⟩),h⟩
  · rintro ⟨hx,h⟩
    refine ⟨h,?_⟩
    rintro (⟨_,rfl⟩ | ⟨rfl,rfl⟩)
    · exact hx rfl
    · exact G.loopless _ h

lemma delete_edge_degree_left (huv : G.Adj u v) :
    (G.deleteEdges {s(u,v)}).degree u + 1 = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,delete_edge_neighbors_left]
  exact Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)

lemma delete_edge_degree_right (huv : G.Adj u v) :
    (G.deleteEdges {s(u,v)}).degree v + 1 = G.degree v := by
  have h := delete_edge_degree_left huv.symm
  rw [show s(v,u) = s(u,v) from Sym2.eq_swap] at h
  exact h

lemma delete_edge_degree_other (hwu : w ≠ u) (hwv : w ≠ v) :
    (G.deleteEdges {s(u,v)}).degree w = G.degree w := by
  have hn : (G.deleteEdges {s(u,v)}).neighborFinset w = G.neighborFinset w := by
    ext x
    simp [SimpleGraph.deleteEdges_adj,Sym2.eq_iff,hwu,hwv]
  exact congrArg Finset.card hn


end Erdos184Work.Compression
