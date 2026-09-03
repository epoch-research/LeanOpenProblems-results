import Submission.ShortTriangleDistinctCubicExclusion

/-! A cubic-pair lift controlled directly by odd residual attachment degree. -/
namespace Erdos583ResidualOddAttachmentDevelopment
open SimpleGraph Erdos583Work Erdos583CubicTriangleOddAttachmentDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cubic_triangle_residual_odd_lift {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hrodd : Odd (Nat.card (G.neighborSet r))) (haodd : Odd (Nat.card ((puncture G ({x,y} : Set V)).neighborSet a)))
    (D : Finset (puncture G ({x,y} : Set V)).Subgraph)
    (hD : GoodDecomposition (puncture G ({x,y} : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let K := puncture G ({x,y} : Set V)
  let Q : G.Walk r b := Walk.cons hrx (Walk.cons hxy (Walk.cons hyb Walk.nil))
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Walk.support,hrx.ne,hry.ne,hbr.symm,hxy.ne,hbx.symm,hyb.ne]
  let F := G.deleteEdges Q.toSubgraph.edgeSet
  have hQe (u v : V) : s(u,v) ∈ Q.toSubgraph.edgeSet ↔
      s(u,v)=s(r,x) ∨ s(u,v)=s(x,y) ∨ s(u,v)=s(y,b) := by
    simp only [Q,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
  have hFxa : F.Adj x a := by
    refine deleteEdges_adj.mpr ⟨hxa,?_⟩
    rw [hQe]
    simp [hrx.ne.symm,har,hay,hxy.ne,hbx.symm]
  have hFyr : F.Adj y r := by
    refine deleteEdges_adj.mpr ⟨hry.symm,?_⟩
    rw [hQe]
    simp [hry.ne.symm,hxy.ne.symm,hrx.ne,hbr.symm,hyb.ne]
  have hcover : F.edgeSet=insert s(y,r) (insert s(x,a) K.edgeSet) := by
    ext e
    induction e using Sym2.ind with
    | h u v =>
      constructor
      · intro he
        have h := deleteEdges_adj.mp he
        rw [hQe] at h
        by_cases hu : u=x
        · subst u
          rcases hNx v h.1 with rfl | rfl | rfl
          · exact (h.2 (Or.inl Sym2.eq_swap)).elim
          · exact (h.2 (Or.inr (Or.inl rfl))).elim
          · exact Or.inr (Or.inl rfl)
        by_cases hu' : u=y
        · subst u
          rcases hNy v h.1 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact (h.2 (Or.inr (Or.inl Sym2.eq_swap))).elim
          · exact (h.2 (Or.inr (Or.inr rfl))).elim
        by_cases hv : v=x
        · subst v
          rcases hNx u h.1.symm with rfl | rfl | rfl
          · exact (h.2 (Or.inl rfl)).elim
          · exact (h.2 (Or.inr (Or.inl Sym2.eq_swap))).elim
          · exact Or.inr (Or.inl Sym2.eq_swap)
        by_cases hv' : v=y
        · subst v
          rcases hNy u h.1.symm with rfl | rfl | rfl
          · exact Or.inl Sym2.eq_swap
          · exact (h.2 (Or.inr (Or.inl rfl))).elim
          · exact (h.2 (Or.inr (Or.inr Sym2.eq_swap))).elim
        exact Or.inr (Or.inr ⟨h.1,by simp [hu,hu'],by simp [hv,hv']⟩)
      · rintro (he|he|he)
        · exact F.adj_congr_of_sym2 he |>.mpr hFyr
        · exact F.adj_congr_of_sym2 he |>.mpr hFxa
        · refine deleteEdges_adj.mpr ⟨he.1,?_⟩
          rw [hQe]
          rintro (h|h|h)
          · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact he.2.2 (Or.inl rfl)
            · exact he.2.1 (Or.inl rfl)
          · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact he.2.1 (Or.inl rfl)
            · exact he.2.2 (Or.inl rfl)
          · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact he.2.1 (Or.inr rfl)
            · exact he.2.2 (Or.inr rfl)
  have hrK : K.neighborSet r=G.neighborSet r \ {x,y} := by
    ext v
    simp [K,mem_neighborSet,puncture_adj,hrx.ne,hry.ne]
  obtain ⟨E,hE,hEc⟩ := append_two_fresh_leaf_edges (K := K) hFxa hFyr hxy.ne hrx.ne.symm hay har
    (fun v hv ↦ hv.2.1 (Or.inl rfl)) (fun v hv ↦ hv.2.1 (Or.inr rfl))
    haodd
    (odd_after_two_neighbors hrx hry hxy.ne hrK hrodd) hcover D hD
  obtain ⟨E',hE',hE'c⟩ := restore_path_subgraph (show IsPathSubgraph Q.toSubgraph from ⟨_,_,Q,hQ,rfl⟩) hE
  exact ⟨E',hE',by omega⟩

end Erdos583ResidualOddAttachmentDevelopment
