import Submission.CubicTriangleSingleton

/-! Consequences of forced endpoint pairing in a fixed path partition. -/
namespace Erdos583LockedEndpointPairDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- Every member ending at `a` is the same member as every one ending at `b`. -/
def EndpointPairLocked {V : Type*} {G : SimpleGraph V}
    (D : Finset G.Subgraph) (a b : V) : Prop :=
  ∀ (u v : V) (P : G.Walk a u) (Q : G.Walk b v),
    P.IsPath → Q.IsPath → P.toSubgraph ∈ D → Q.toSubgraph ∈ D →
      P.toSubgraph=Q.toSubgraph

lemma path_endpoint_edge_singleton {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (hP : P.IsPath) (he : s(a,b) ∈ P.edges) :
    P.toSubgraph.edgeSet={s(a,b)} := by
  cases P with
  | nil => simp at he
  | @cons _ x _ h Q =>
    have hbx : b=x := by simpa using hP.eq_snd_of_mem_edges he
    subst x
    have hQ : Q=Walk.nil := (Walk.isPath_iff_eq_nil Q).mp hP.of_cons
    simp [hQ]

lemma locked_pair_path {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D) {a b : V} (hab : a ≠ b)
    (hlock : EndpointPairLocked D a b)
    (ha : 0 < endpointMultiplicity D a) (hb : 0 < endpointMultiplicity D b) :
    ∃ P : G.Walk a b, P.IsPath ∧ P.toSubgraph ∈ D := by
  obtain ⟨u,P,hP,hPD⟩ := MarkedBudgets.marked_of_positive_endpoint hD ha
  obtain ⟨v,Q,hQ,hQD⟩ := MarkedBudgets.marked_of_positive_endpoint hD hb
  have he := hlock u v P Q hP hQ hPD hQD
  have hbend := MarkedBudgets.endpoint_of_path_rep Q hQ P hP.isTrail he
  rcases hbend with hba | hbu
  · exact (hab hba.symm).elim
  · subst u
    exact ⟨P,hP,hPD⟩

lemma locked_pair_member_unique {V : Type*} {G : SimpleGraph V}
    {D : Finset G.Subgraph} {a b : V} (hlock : EndpointPairLocked D a b)
    (P : G.Walk a b) (hP : P.IsPath) (hPD : P.toSubgraph ∈ D)
    {u v : V} (Q : G.Walk u v) (hQ : Q.IsPath) (hQD : Q.toSubgraph ∈ D)
    (he : u=a ∨ u=b ∨ v=a ∨ v=b) : Q.toSubgraph=P.toSubgraph := by
  rcases he with h | h | h | h
  · subst u
    simpa using hlock v a Q P.reverse hQ hP.reverse hQD (by simpa using hPD)
  · subst u
    exact (hlock b v P Q hP hQ hPD hQD).symm
  · subst v
    simpa using hlock u a Q.reverse P.reverse hQ.reverse hP.reverse
      (by simpa using hQD) (by simpa using hPD)
  · subst v
    simpa using (hlock b u P Q.reverse hP hQ.reverse hPD (by simpa using hQD)).symm

lemma locked_pair_endpointMultiplicity {V : Type*} {G : SimpleGraph V}
    {D : Finset G.Subgraph} {a b : V} (hab : a ≠ b) (hlock : EndpointPairLocked D a b)
    (P : G.Walk a b) (hP : P.IsPath) (hPD : P.toSubgraph ∈ D)
    (hD : ∀ H ∈ D, IsPathSubgraph H) :
    endpointMultiplicity D a=1 ∧ endpointMultiplicity D b=1 := by
  classical
  have hn : ¬P.Nil := fun h ↦ hab h.eq
  have hPa : (P.toSubgraph.neighborSet a).ncard=1 := by
    rw [hP.neighborSet_toSubgraph_startpoint hn,Set.ncard_singleton]
  have hPb : (P.toSubgraph.neighborSet b).ncard=1 := by
    rw [hP.neighborSet_toSubgraph_endpoint hn,Set.ncard_singleton]
  have hone {z : V} (hz : z=a ∨ z=b) (hPz : (P.toSubgraph.neighborSet z).ncard=1) :
      endpointMultiplicity D z=1 := by
    have hf : D.filter (fun H ↦ (H.neighborSet z).ncard=1)={P.toSubgraph} := by
      ext H
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨hHD,hHz⟩
        obtain ⟨u,Q,hQ,hHe⟩ := path_endpoint_of_neighbor_ncard_one (hD H hHD) hHz
        rw [hHe]
        exact locked_pair_member_unique hlock P hP hPD Q hQ (hHe ▸ hHD)
          (hz.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
      · rintro rfl
        exact ⟨hPD,hPz⟩
    change (D.filter (fun H ↦ (H.neighborSet z).ncard=1)).card=1
    rw [hf,Finset.card_singleton]
  exact ⟨hone (Or.inl rfl) hPa,hone (Or.inr rfl) hPb⟩

lemma locked_pair_edge_internal {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D) {a b : V}
    (hab : G.Adj a b) (hlock : EndpointPairLocked D a b)
    (ha : 0 < endpointMultiplicity D a) (hb : 0 < endpointMultiplicity D b)
    (hnot : ∀ K ∈ D, K.edgeSet ≠ {s(a,b)}) :
    ∃ P : G.Walk a b, ∃ u v, ∃ Q : G.Walk u v,
      P.IsPath ∧ P.toSubgraph ∈ D ∧ s(a,b) ∉ P.edges ∧
      Q.IsPath ∧ Q.toSubgraph ∈ D ∧ s(a,b) ∈ Q.edges ∧
      Q.toSubgraph ≠ P.toSubgraph ∧
      a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧
      (Q.toSubgraph.neighborSet a).ncard=2 ∧ (Q.toSubgraph.neighborSet b).ncard=2 := by
  classical
  obtain ⟨P,hP,hPD⟩ := locked_pair_path hD hab.ne hlock ha hb
  have hnP : s(a,b) ∉ P.edges := fun he ↦ hnot _ hPD (path_endpoint_edge_singleton P hP he)
  have heG : s(a,b) ∈ G.edgeSet := hab
  rw [←hD.2.2] at heG
  obtain ⟨K,hKD,heK⟩ := Set.mem_iUnion₂.mp heG
  obtain ⟨u,v,Q,hQ,hKe⟩ := hD.1 K hKD
  have hQD : Q.toSubgraph ∈ D := hKe ▸ hKD
  have heQ : s(a,b) ∈ Q.edges := Q.mem_edges_toSubgraph.mp (hKe ▸ heK)
  have hneq : Q.toSubgraph ≠ P.toSubgraph := by
    intro hh
    exact hnP (P.mem_edges_toSubgraph.mp (hh ▸ Q.mem_edges_toSubgraph.mpr heQ))
  have hends : ¬(u=a ∨ u=b ∨ v=a ∨ v=b) := fun hh ↦
    hneq (locked_pair_member_unique hlock P hP hPD Q hQ hQD hh)
  have hau : a ≠ u := fun h ↦ hends (Or.inl h.symm)
  have hav : a ≠ v := fun h ↦ hends (Or.inr (Or.inr (Or.inl h.symm)))
  have hbu : b ≠ u := fun h ↦ hends (Or.inr (Or.inl h.symm))
  have hbv : b ≠ v := fun h ↦ hends (Or.inr (Or.inr (Or.inr h.symm)))
  have hnQ : ¬Q.Nil := by intro hh; cases hh; simp at heQ
  have has : a ∈ Q.support := Q.fst_mem_support_of_mem_edges heQ
  have hbs : b ∈ Q.support := Q.snd_mem_support_of_mem_edges heQ
  have hda : (Q.toSubgraph.neighborSet a).ncard=2 := by
    rw [path_neighbor_ncard_formula hQ hnQ]; simp [hau,hav,has]
  have hdb : (Q.toSubgraph.neighborSet b).ncard=2 := by
    rw [path_neighbor_ncard_formula hQ hnQ]; simp [hbu,hbv,hbs]
  exact ⟨P,u,v,Q,hP,hPD,hnP,hQ,hQD,heQ,hneq,hau,hav,hbu,hbv,hda,hdb⟩

end Erdos583LockedEndpointPairDevelopment
