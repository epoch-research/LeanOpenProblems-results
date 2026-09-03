import Submission.ResidualOddAttachment

/-! A fresh shortcut repairs cubic true twins at an even common external attachment. -/
namespace Erdos583CubicTwinsFreshDevelopment
open SimpleGraph Erdos583Work Erdos583SupportSmoothingDevelopment
open Erdos583PrivateProxyDevelopment Erdos583QuarticPairProxyDevelopment
open Erdos583CubicTriangleEvenAttachmentDevelopment Erdos583LeafPunctureDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cubic_twins_fresh_even_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a : Fin n}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hya : G.Adj y a) (har : a ≠ r)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=a)
    (hno : ¬G.Adj r a) (haeven : Even (Nat.card (G.neighborSet a)))
    (hK : SupportConnected (puncture G ({x,y} : Set (Fin n))))
    (hra : (puncture G ({x,y} : Set (Fin n))).Reachable r a) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let K := puncture G ({x,y} : Set (Fin n))
  let F := puncture G ({y} : Set (Fin n))
  let H := smooth F x r a
  have hFxr : F.Adj x r := ⟨hrx.symm,hxy.ne,hry.ne⟩
  have hFxa : F.Adj x a := ⟨hxa,hxy.ne,hya.ne.symm⟩
  have hNxF : ∀ z, F.Adj x z → z=r ∨ z=a := by
    intro z hz
    rcases hNx z hz.1 with hh | hh | hh
    · exact Or.inl hh
    · exact (hz.2.2 hh).elim
    · exact Or.inr hh
  have hHS : H=K ⊔ edge r a := by
    ext u v
    simp only [H,F,K,smooth,sup_adj,puncture_adj,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  have hH : SupportConnected H := by
    rw [hHS]
    exact connected_support_add_supported_edge hK (mem_support_of_reachable har.symm hra)
      (mem_support_of_reachable har hra.symm)
  have hxH : x ∉ H.support := by
    rw [hHS]
    exact puncture_fresh_internal (T := ({x,y} : Set (Fin n))) (Or.inl rfl) hrx.ne.symm hxa.ne
  have hyH : y ∉ H.support := by
    rw [hHS]
    exact puncture_fresh_internal (T := ({x,y} : Set (Fin n))) (Or.inr rfl) hry.ne.symm hya.ne
  apply gallai_private_pair_proxy hsmall G H hxy.ne hH hxH hyH
  intro D hD
  obtain ⟨E,hE,hEc⟩ := smooth_lift hFxr hFxa har.symm hNxF (fun h ↦ hno h.1) D hD
  let Q := Walk.cons hry (Walk.cons hxy.symm Walk.nil)
  have hQ : Q.IsPath := by simp [Q,Walk.cons_isPath_iff,hry.ne,hrx.ne,hxy.ne.symm]
  let J := G.deleteEdges Q.toSubgraph.edgeSet
  have hyaJ : J.Adj y a := deleteEdges_adj.mpr ⟨hya,by
    simp [Q,hry.ne.symm,hxy.ne.symm,har,hxa.ne.symm]⟩
  have hNyJ : ∀ z, J.Adj y z → z=a := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNy z hz with hh | hh | hh
    · subst z; exact (hnz (by simp [Q,Sym2.eq_swap])).elim
    · subst z; exact (hnz (by simp [Q])).elim
    · exact hh
  have hJF : puncture J ({y} : Set (Fin n))=F := by
    ext u v
    simp only [J,F,puncture_adj,deleteEdges_adj,Set.mem_singleton_iff]
    constructor
    · tauto
    · rintro ⟨huv,hu,hv⟩
      refine ⟨⟨huv,?_⟩,hu,hv⟩
      simp [Q,hu,hv]
  have hJe : J.edgeSet=insert s(y,a) F.edgeSet := by
    have hh := puncture_leaf_edgeSet hyaJ hNyJ
    rw [hJF] at hh
    rw [hh,Set.union_comm,Set.singleton_union]
  have hFJ : F ≤ J := by
    intro u v huv
    change s(u,v) ∈ J.edgeSet
    rw [hJe]
    exact Or.inr huv
  have haF : F.neighborSet a=G.neighborSet a \ {y} := by
    ext z
    simp [F,puncture_adj,hya.ne.symm]
  obtain ⟨E',hE',hE'c⟩ := DegreeThreeReduction.append_at_odd_to_isolated hFJ hyaJ
    (fun z hz ↦ hz.2.1 rfl) (odd_after_one_neighbor hya.symm haF haeven) hJe E hE
  obtain ⟨E'',hE'',hE''c⟩ := restore_path_subgraph ⟨_,_,Q,hQ,rfl⟩ hE'
  exact ⟨E'',hE'',by omega⟩

end Erdos583CubicTwinsFreshDevelopment
