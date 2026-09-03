import Submission.CubicTriangleCarrier

/-! Parity-controlled restoration at a cubic triangle pair. -/
namespace Erdos583CubicTriangleOddAttachmentDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.DegreeThreeReduction Erdos583Work.BridgeGlue
open Erdos583CubicTriangleReductionDevelopment Erdos583CubicTriangleCarrierDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma append_two_fresh_leaf_edges {V : Type*} [Fintype V] {K F : SimpleGraph V}
    {x a y r : V} (hxa : F.Adj x a) (hyr : F.Adj y r)
    (hxy : x ≠ y) (hxr : x ≠ r) (hay : a ≠ y) (har : a ≠ r)
    (hxiso : ∀ v, ¬K.Adj x v) (hyiso : ∀ v, ¬K.Adj y v)
    (haodd : Odd (Nat.card (K.neighborSet a))) (hrodd : Odd (Nat.card (K.neighborSet r)))
    (hcover : F.edgeSet=insert s(y,r) (insert s(x,a) K.edgeSet))
    (D : Finset K.Subgraph) (hD : GoodDecomposition K D) :
    ∃ E : Finset F.Subgraph, GoodDecomposition F E ∧ E.card ≤ D.card := by
  classical
  let B := F.deleteEdges {s(y,r)}
  have hne : s(x,a) ≠ s(y,r) := by simp [hxy,hxr]
  have hnK : s(y,r) ∉ K.edgeSet := fun h ↦ hyiso r h
  have hBe : B.edgeSet=insert s(x,a) K.edgeSet := by
    rw [edgeSet_deleteEdges,hcover]
    ext e
    simp only [Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · tauto
    · rintro (rfl|h)
      · exact ⟨Or.inr (Or.inl rfl),hne⟩
      · exact ⟨Or.inr (Or.inr h),fun he ↦ hnK (he ▸ h)⟩
  have hKB : K ≤ B := by intro u v huv; change s(u,v) ∈ B.edgeSet; rw [hBe]; exact Or.inr huv
  have hBxa : B.Adj x a := deleteEdges_adj.mpr ⟨hxa,hne⟩
  obtain ⟨E,hE,hEc⟩ := append_at_odd_to_isolated hKB hBxa hxiso haodd hBe D hD
  have hyB : ∀ v, ¬B.Adj y v := by
    intro v hv
    change s(y,v) ∈ B.edgeSet at hv
    rw [hBe] at hv
    rcases hv with hv | hv
    · rcases Sym2.eq_iff.mp hv with ⟨h,_⟩ | ⟨h,_⟩
      · exact hxy h.symm
      · exact hay h.symm
    · exact hyiso v hv
  have hrB : B.neighborSet r=K.neighborSet r := by
    ext v
    change s(r,v) ∈ B.edgeSet ↔ s(r,v) ∈ K.edgeSet
    rw [hBe]
    simp only [Set.mem_insert_iff]
    constructor
    · rintro (h|h)
      · rcases Sym2.eq_iff.mp h with ⟨h,_⟩ | ⟨h,_⟩
        · exact (hxr h.symm).elim
        · exact (har h.symm).elim
      · exact h
    · exact Or.inr
  have hF : F.edgeSet=insert s(y,r) B.edgeSet := by rw [hBe,hcover]
  obtain ⟨E',hE',hE'c⟩ := append_at_odd_to_isolated (show B ≤ F from deleteEdges_le _)
    hyr hyB (hrB.symm ▸ hrodd) hF E hE
  exact ⟨E',hE',hE'c.trans hEc⟩

lemma odd_after_two_neighbors {V : Type*} [Fintype V] {K G : SimpleGraph V}
    {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b)
    (hN : K.neighborSet v=G.neighborSet v \ {a,b}) (ho : Odd (Nat.card (G.neighborSet v))) :
    Odd (Nat.card (K.neighborSet v)) := by
  have hsub : ({a,b} : Set V) ⊆ G.neighborSet v := by rintro u (rfl|rfl) <;> assumption
  have hh := Set.ncard_diff_add_ncard_of_subset hsub
  rw [←hN,Set.ncard_pair hab,←Nat.card_coe_set_eq,←Nat.card_coe_set_eq] at hh
  simp only [Nat.odd_iff] at ho ⊢
  omega

lemma cubic_triangle_odd_attachment_lift {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b) (hab : G.Adj a b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hrodd : Odd (Nat.card (G.neighborSet r))) (haodd : Odd (Nat.card (G.neighborSet a)))
    (D : Finset (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Subgraph)
    (hD : GoodDecomposition (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let K := puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)
  let Q : G.Walk r a := Walk.cons hrx (Walk.cons hxy (Walk.cons hyb (Walk.cons hab.symm Walk.nil)))
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Walk.support,hrx.ne,hry.ne,hbr.symm,har.symm,hxy.ne,hbx.symm,hxa.ne,
      hyb.ne,hay.symm,hab.ne.symm]
  let F := G.deleteEdges Q.toSubgraph.edgeSet
  have hQe (u v : V) : s(u,v) ∈ Q.toSubgraph.edgeSet ↔
      s(u,v)=s(r,x) ∨ s(u,v)=s(x,y) ∨ s(u,v)=s(y,b) ∨ s(u,v)=s(b,a) := by
      simp only [Q,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false]
  have hFxa : F.Adj x a := by
    refine deleteEdges_adj.mpr ⟨hxa,?_⟩
    rw [hQe]
    simp [hrx.ne.symm,har,hay,hxy.ne,hxa.ne,hbx.symm,hab.ne]
  have hFyr : F.Adj y r := by
    refine deleteEdges_adj.mpr ⟨hry.symm,?_⟩
    rw [hQe]
    simp [hry.ne.symm,hxy.ne.symm,hrx.ne,hbr.symm,hyb.ne,hay.symm]
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
          · exact (h.2 (Or.inr (Or.inr (Or.inl rfl)))).elim
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
          · exact (h.2 (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))).elim
        refine Or.inr (Or.inr ⟨deleteEdges_adj.mpr ⟨h.1,?_⟩,by simp [hu,hu'],by simp [hv,hv']⟩)
        intro he
        exact h.2 (Or.inr (Or.inr (Or.inr (he.trans Sym2.eq_swap))))
      · rintro (he|he|he)
        · exact F.adj_congr_of_sym2 he |>.mpr hFyr
        · exact F.adj_congr_of_sym2 he |>.mpr hFxa
        · have he' := deleteEdges_adj.mp he.1
          refine deleteEdges_adj.mpr ⟨he'.1,?_⟩
          rw [hQe]
          rintro (h|h|h|h)
          · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact he.2.2 (Or.inl rfl)
            · exact he.2.1 (Or.inl rfl)
          · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact he.2.1 (Or.inl rfl)
            · exact he.2.2 (Or.inl rfl)
          · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact he.2.1 (Or.inr rfl)
            · exact he.2.2 (Or.inr rfl)
          · exact he'.2 (h.trans Sym2.eq_swap)
  have hrK : K.neighborSet r=G.neighborSet r \ {x,y} := by
    ext v
    simp only [K,mem_neighborSet,puncture_adj,deleteEdges_adj,Set.mem_singleton_iff,
      Set.mem_insert_iff,Set.mem_diff,hrx.ne,hry.ne,false_or,not_false_eq_true,true_and]
    constructor
    · tauto
    · rintro ⟨h,hv⟩
      refine ⟨⟨h,?_⟩,hv⟩
      simp [har.symm,hbr.symm]
  have haK : K.neighborSet a=G.neighborSet a \ {x,b} := by
    have hnay : ¬G.Adj a y := by
      intro h
      rcases hNy a h.symm with h | h | h
      · exact har h
      · exact hxa.ne h.symm
      · exact hab.ne h
    ext v
    simp only [K,mem_neighborSet,puncture_adj,deleteEdges_adj,Set.mem_singleton_iff,
      Set.mem_insert_iff,Set.mem_diff,hxa.ne.symm,hay,false_or,not_false_eq_true,true_and]
    constructor
    · rintro ⟨⟨h,he⟩,hv⟩
      exact ⟨h,by rintro (rfl|rfl); exact hv (Or.inl rfl); exact he rfl⟩
    · rintro ⟨h,hv⟩
      refine ⟨⟨h,?_⟩,?_⟩
      · simp only [Sym2.eq_iff]
        rintro (⟨_,he⟩|⟨he,_⟩)
        · exact hv (Or.inr he)
        · exact hab.ne he
      · rintro (rfl|rfl)
        · exact hv (Or.inl rfl)
        · exact hnay h
  obtain ⟨E,hE,hEc⟩ := append_two_fresh_leaf_edges (K := K) hFxa hFyr hxy.ne hrx.ne.symm hay har
    (fun v hv ↦ hv.2.1 (Or.inl rfl)) (fun v hv ↦ hv.2.1 (Or.inr rfl))
    (odd_after_two_neighbors hxa.symm hab hbx.symm haK haodd)
    (odd_after_two_neighbors hrx hry hxy.ne hrK hrodd) hcover D hD
  obtain ⟨E',hE',hE'c⟩ := restore_path_subgraph (show IsPathSubgraph Q.toSubgraph from ⟨_,_,Q,hQ,rfl⟩) hE
  exact ⟨E',hE',by omega⟩

end Erdos583CubicTriangleOddAttachmentDevelopment
