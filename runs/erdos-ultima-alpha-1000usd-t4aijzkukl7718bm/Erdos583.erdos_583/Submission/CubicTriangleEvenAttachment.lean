import Submission.CubicTriangleEvenChord

/-! The complementary parity repair: an even external attachment at an odd root. -/
namespace Erdos583CubicTriangleEvenAttachmentDevelopment
open SimpleGraph Erdos583Work
open Erdos583CubicTriangleOddAttachmentDevelopment Erdos583CubicTrianglePunctureDevelopment
open Erdos583CubicTriangleCarrierDevelopment Erdos583CubicTriangleEvenChordDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma odd_after_one_neighbor {V : Type*} [Fintype V] {K G : SimpleGraph V}
    {v x : V} (hx : G.Adj v x)
    (hN : K.neighborSet v=G.neighborSet v \ {x}) (he : Even (Nat.card (G.neighborSet v))) :
    Odd (Nat.card (K.neighborSet v)) := by
  have hh := Set.ncard_diff_singleton_add_one (show x ∈ G.neighborSet v from hx)
  rw [←hN,←Nat.card_coe_set_eq,←Nat.card_coe_set_eq] at hh
  rw [←hh] at he
  exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he)

lemma cubic_triangle_even_attachment_lift {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hrodd : Odd (Nat.card (G.neighborSet r))) (haeven : Even (Nat.card (G.neighborSet a)))
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
    simp [hrx.ne.symm,har,hay,hxy.ne,hbx.symm,hab]
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
  have haK : K.neighborSet a=G.neighborSet a \ {x} := by
    have hnay : ¬G.Adj a y := by
      intro h
      rcases hNy a h.symm with h | h | h
      · exact har h
      · exact hxa.ne h.symm
      · exact hab h
    ext v
    simp only [K,mem_neighborSet,puncture_adj,Set.mem_singleton_iff,
      Set.mem_insert_iff,Set.mem_diff,hxa.ne.symm,hay,false_or,not_false_eq_true,true_and]
    constructor
    · rintro ⟨h,hv⟩
      exact ⟨h,fun hh ↦ hv (Or.inl hh)⟩
    · rintro ⟨h,hv⟩
      exact ⟨h,by rintro (rfl|rfl); exact hv rfl; exact hnay h⟩
  obtain ⟨E,hE,hEc⟩ := append_two_fresh_leaf_edges (K := K) hFxa hFyr hxy.ne hrx.ne.symm hay har
    (fun v hv ↦ hv.2.1 (Or.inl rfl)) (fun v hv ↦ hv.2.1 (Or.inr rfl))
    (odd_after_one_neighbor hxa.symm haK haeven)
    (odd_after_two_neighbors hrx hry hxy.ne hrK hrodd) hcover D hD
  obtain ⟨E',hE',hE'c⟩ := restore_path_subgraph (show IsPathSubgraph Q.toSubgraph from ⟨_,_,Q,hQ,rfl⟩) hE
  exact ⟨E',hE',by omega⟩

lemma cubic_pair_puncture_connected {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {r x y a b : V}
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hra : (puncture G ({x,y} : Set V)).Reachable r a)
    (hrb : (puncture G ({x,y} : Set V)).Reachable r b) :
    SupportConnected (puncture G ({x,y} : Set V)) := by
  classical
  let S : Set V := {x,y}
  let K := puncture G S
  let f (v : V) := if v ∈ S then r else v
  have hboundary {t z} (ht : t ∈ S) (hz : z ∉ S) (htz : G.Adj t z) : K.Reachable r z := by
    rcases ht with rfl | rfl
    · rcases hNx z htz with rfl | rfl | rfl
      · exact .rfl
      · exact (hz (Or.inr rfl)).elim
      · exact hra
    · rcases hNy z htz with rfl | rfl | rfl
      · exact .rfl
      · exact (hz (Or.inl rfl)).elim
      · exact hrb
  apply hG.of_reachable_map f (support_mono (puncture_le G S))
  · intro u v huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · simp only [f,if_pos hu,if_pos hv]; exact .rfl
    · simp only [f,if_pos hu,if_neg hv]; exact hboundary hu hv huv
    · simp only [f,if_neg hu,if_pos hv]; exact (hboundary hv hu huv.symm).symm
    · simp only [f,if_neg hu,if_neg hv]
      exact (show K.Adj u v from ⟨huv,hu,hv⟩).reachable
  · intro u hu
    obtain ⟨v,hv⟩ := hu
    simp only [f,if_neg hv.2.1]
    exact .rfl

lemma cubic_triangle_even_attachment_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y a b : Fin n}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hrodd : Odd (Nat.card (G.neighborSet r))) (haeven : Even (Nat.card (G.neighborSet a)))
    (hra : (puncture G ({x,y} : Set (Fin n))).Reachable r a)
    (hrb : (puncture G ({x,y} : Set (Fin n))).Reachable r b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let K := puncture G ({x,y} : Set (Fin n))
  have hK : SupportConnected K := cubic_pair_puncture_connected
    (fun u _ v _ ↦ hG.preconnected u v) hNx hNy hra hrb
  have hsub : K.support ⊆ G.support \ {x,y} := by
    rintro u ⟨v,hv⟩
    exact ⟨⟨v,hv.1⟩,hv.2.1⟩
  have hpair : ({x,y} : Set (Fin n)) ⊆ G.support := by
    rintro u (rfl|rfl)
    · exact ⟨r,hrx.symm⟩
    · exact ⟨r,hry.symm⟩
  have hcard := support_card_bound_of_removed hpair hsub
  rw [Set.ncard_pair hxy.ne] at hcard
  have hGcard : G.support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using G.support.ncard_le_card
  apply LowDegreeAdjacency.gallai_of_two_vertex_support_reduction hsmall G K hK (by omega)
  intro D hD
  exact cubic_triangle_even_attachment_lift hrx hry hxy hxa hyb har hay hbr hbx hab hNx hNy hrodd haeven D hD

end Erdos583CubicTriangleEvenAttachmentDevelopment
