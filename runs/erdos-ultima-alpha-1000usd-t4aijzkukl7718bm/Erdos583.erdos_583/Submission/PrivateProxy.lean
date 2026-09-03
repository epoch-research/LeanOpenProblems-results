import Submission.MixedTriangleTerminalExclusion

/-! Connectivity and path-budget tools for replacing two private vertices by a proxy edge. -/
namespace Erdos583PrivateProxyDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma support_connected_of_private_boundary {V : Type*} {G H : SimpleGraph V}
    (hG : G.Connected) (S : Set V) (r : V)
    (hmiss : ∀ z ∈ S, z ∉ H.support)
    (hrest : ∀ u, u ∉ S → ∀ v, v ∉ S → G.Adj u v → H.Reachable u v)
    (hbdy : ∀ u ∈ S, ∀ v, v ∉ S → G.Adj u v → H.Reachable r v) :
    SupportConnected H := by
  classical
  let f (z : V) := if z ∈ S then r else z
  have hedge (u v : V) (huv : G.Adj u v) : H.Reachable (f u) (f v) := by
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · simp only [f,if_pos hu,if_pos hv]; exact .rfl
    · simp only [f,if_pos hu,if_neg hv]; exact hbdy u hu v hv huv
    · simp only [f,if_neg hu,if_pos hv]; exact (hbdy v hv u hu huv.symm).symm
    · simp only [f,if_neg hu,if_neg hv]; exact hrest u hu v hv huv
  intro u hu v hv
  have hun : u ∉ S := fun hh ↦ hmiss u hh hu
  have hvn : v ∉ S := fun hh ↦ hmiss v hh hv
  simpa only [f,if_neg hun,if_neg hvn] using
    reachable_map_to_reachable f hedge (hG.preconnected u v)

lemma mixed_boundary_connected {V : Type*} {G H : SimpleGraph V}
    (hG : G.Connected) {r x y a b c : V}
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c)
    (hx : x ∉ H.support) (hy : y ∉ H.support)
    (hrest : ∀ u, u ∉ ({x,y} : Set V) → ∀ v, v ∉ ({x,y} : Set V) →
      G.Adj u v → H.Reachable u v)
    (hra : H.Reachable r a) (hrb : H.Reachable r b) (hrc : H.Reachable r c) :
    SupportConnected H := by
  refine support_connected_of_private_boundary hG ({x,y} : Set V) r ?_ hrest ?_
  · rintro z (rfl|rfl) <;> assumption
  · rintro u (rfl|rfl) v hv huv
    · rcases hNx v huv with rfl | rfl | rfl | rfl
      · exact .rfl
      · exact (hv (Or.inr rfl)).elim
      · exact hra
      · exact hrb
    · rcases hNy v huv with rfl | rfl | rfl
      · exact .rfl
      · exact (hv (Or.inl rfl)).elim
      · exact hrc

lemma proxy_residual_edgeSet {V : Type*} (K : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    (K ⊔ edge a b).edgeSet \ {s(a,b)}=K.edgeSet \ {s(a,b)} := by
  rw [edgeSet_sup,edge_edgeSet_of_ne hab]
  ext e
  simp only [Set.mem_diff,Set.mem_union,Set.mem_singleton_iff]
  tauto

lemma puncture_proxy_restore_at_start {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {a b d : V} (hab : a ≠ b)
    (P : G.Walk a b) (hP : P.IsPath) (Q : G.Walk a d) (hQ : Q.IsPath)
    (hfresh : ∀ z ∈ P.support, z ≠ a → z ≠ b → z ∈ S)
    (hpatch : ∀ t ∈ S, ∀ z, G.Adj t z → s(t,z) ∈ P.edges ∨ s(t,z) ∈ Q.edges)
    (htouch : ∀ e ∈ Q.edges, ∃ t ∈ S, t ∈ e)
    (hQP : List.Disjoint Q.edges P.edges) (hproxy : s(a,b) ∉ P.edges) (hbQ : b ∉ Q.support)
    (D : Finset (puncture G S ⊔ edge a b).Subgraph)
    (hD : GoodDecomposition (puncture G S ⊔ edge a b) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  by_cases he : (puncture G S).Adj a b
  · let R := Walk.cons he.1.symm Q
    have hR : R.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hQ,hbQ⟩
    have hQK := puncture_disjoint_walk S Q htouch
    have hcover := puncture_two_walks_cover S P Q hpatch
    apply hD.expand_edge_restore_path
      (Or.inr ((edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)) P hP R hR
    · intro z hz hza hzb
      exact puncture_fresh_internal (hfresh z hz hza hzb) hza hzb
    · rw [proxy_residual_edgeSet _ hab,hcover]
      ext e
      simp only [R,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,
        Set.mem_union,Set.mem_diff,Set.mem_singleton_iff,Sym2.eq_swap (a := b) (b := a)]
      constructor
      · tauto
      · rintro ((⟨hh,_⟩|hh)|(hh|hh))
        · exact Or.inl (Or.inl hh)
        · exact Or.inl (Or.inr hh)
        · exact Or.inl (Or.inl (hh ▸ he))
        · exact Or.inr hh
    · apply Set.disjoint_left.mpr
      intro e heR heP
      have heP' := P.mem_edges_toSubgraph.mp heP
      rcases (show e=s(a,b) ∨ e ∈ Q.edges by
        simpa only [R,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,Sym2.eq_swap (a := b) (b := a)] using heR) with hh | hh
      · exact hproxy (hh ▸ heP')
      · exact List.disjoint_left.mp hQP hh heP'
    · rw [proxy_residual_edgeSet _ hab]
      apply Set.disjoint_left.mpr
      intro e heR heK
      rcases (show e=s(a,b) ∨ e ∈ Q.edges by
        simpa only [R,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,Sym2.eq_swap (a := b) (b := a)] using heR) with hh | hh
      · exact heK.2 hh
      · exact Set.disjoint_left.mp hQK (Q.mem_edges_toSubgraph.mpr hh) heK.1
  · exact hD.puncture_expand_restore S hab he P hP Q hQ hfresh hpatch htouch hQP

lemma gallai_private_pair_proxy {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (G H : SimpleGraph (Fin n)) {x y : Fin n} (hxy : x ≠ y)
    (hH : SupportConnected H) (hx : x ∉ H.support) (hy : y ∉ H.support)
    (hlift : ∀ D : Finset H.Subgraph, GoodDecomposition H D →
      ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  apply LowDegreeAdjacency.gallai_of_two_vertex_support_reduction hsmall G H hH _ hlift
  simpa only [Fintype.card_fin] using TipParity.support_card_bound_two_missing H hxy hx hy

end Erdos583PrivateProxyDevelopment
