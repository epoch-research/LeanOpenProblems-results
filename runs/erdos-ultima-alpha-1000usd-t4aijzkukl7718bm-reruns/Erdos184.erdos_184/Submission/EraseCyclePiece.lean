import Submission.Cycles

/-! Removing a specified piece from a decomposition and rebasing the rest. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma erase_cycle_piece {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (H : G.Subgraph) (hH : H ∈ D) :
    ∃ E : Finset (G \ H.spanningCoe).Subgraph,
      (∀ J ∈ E, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (G \ H.spanningCoe) E ∧ E.card + 1 ≤ D.card := by
  let A := G \ H.spanningCoe
  have hle (K : {K // K ∈ D.erase H}) : K.val.spanningCoe ≤ A := by
    intro u v huv
    refine ⟨K.val.adj_sub huv,?_⟩
    intro hHuv
    exact Set.disjoint_left.mp (hd.1 (Finset.mem_erase.mp K.property).2 hH
      (Finset.mem_erase.mp K.property).1)
      (show s(u,v) ∈ K.val.edgeSet from huv) (show s(u,v) ∈ H.edgeSet from hHuv)
  let J : {K // K ∈ D.erase H} → A.Subgraph := fun K => {
    verts := K.val.verts
    Adj := K.val.Adj
    adj_sub := fun h => hle K h
    edge_vert := K.val.edge_vert
    symm := K.val.symm }
  let E := Finset.univ.image J
  have hcard : E.card ≤ (D.erase H).card := by
    exact Finset.card_image_le.trans_eq (by rw [Finset.card_univ,Fintype.card_coe])
  have herase := Finset.card_erase_add_one hH
  refine ⟨E,?_,⟨?_,?_⟩,by omega⟩
  · intro K hK
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hK
    have hh := hc L.val (Finset.mem_erase.mp L.property).2
    refine ⟨hh.1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh.2 v
  · intro K hK L hL hne
    obtain ⟨X,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨Y,_,rfl⟩ := Finset.mem_image.mp hL
    apply hd.1 (Finset.mem_erase.mp X.property).2 (Finset.mem_erase.mp Y.property).2
    intro heq
    exact hne (congrArg J (Subtype.ext heq))
  · ext e
    constructor
    · rintro ⟨_,⟨K,rfl⟩,_,⟨_,rfl⟩,heK⟩
      exact K.edgeSet_subset heK
    · intro he
      have heA : e ∈ G.edgeSet \ H.edgeSet := by
        rw [SimpleGraph.edgeSet_sdiff] at he
        exact he
      have heG := heA.1
      rw [← hd.2] at heG
      obtain ⟨K,hK,heK⟩ := Set.mem_iUnion₂.mp heG
      have hKH : K ≠ H := fun h => heA.2 (h ▸ heK)
      let X : {K // K ∈ D.erase H} := ⟨K,Finset.mem_erase.mpr ⟨hKH,hK⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨J X,Finset.mem_image.mpr ⟨X,Finset.mem_univ _,rfl⟩,heK⟩

end Erdos184
