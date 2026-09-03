import Submission.CountThreeOrder

/-! Exact vertex-deletion edge budgets for induced cycles. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleOutsideBudget
open HighGirthCritical EvenCycleCore
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma no_two_comap {W : Type*} [Fintype W] {G : SimpleGraph V}
    (hG : NoTwoCycles G) (f : W ↪ V) : NoTwoCycles (G.comap f) := by
  let φ : G.comap f →g G := ⟨f,fun h => h⟩
  intro P Q hp hq hd
  have hp' := subgraph_image_cycle_of_injective φ f.injective P hp.1 (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hp.2 v)
  have hq' := subgraph_image_cycle_of_injective φ f.injective Q hq.1 (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hq.2 v)
  apply hG (P.map φ) (Q.map φ) hp' hq'
  rw [Subgraph.edgeSet_map,Subgraph.edgeSet_map]
  apply Set.disjoint_left.mpr
  rintro e ⟨a,ha,hea⟩ ⟨b,hb,heb⟩
  have hab := Sym2.map.injective f.injective (hea.trans heb.symm)
  exact Set.disjoint_left.mp hd ha (hab ▸ hb)

lemma deletion_edges_partition (G : SimpleGraph V) (S : Set V) :
    G.edgeFinset = (avoid G S).edgeFinset ∪ S.toFinset.biUnion (fun v => G.incidenceFinset v) := by
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | h x y =>
      have hxy : G.Adj x y := G.mem_edgeFinset.mp he
      by_cases hx : x ∈ S
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨x,Set.mem_toFinset.mpr hx,by simpa using hxy⟩)
      by_cases hy : y ∈ S
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨y,Set.mem_toFinset.mpr hy,by rw [mem_incidenceFinset,mk'_mem_incidenceSet_right_iff]; exact hxy⟩)
      · exact Finset.mem_union_left _ ((avoid G S).mem_edgeFinset.mpr ⟨hxy,hx,hy⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · exact G.mem_edgeFinset.mpr (edgeSet_mono (avoid_le G S) ((avoid G S).mem_edgeFinset.mp he))
    · obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp he
      exact G.incidenceFinset_subset v hv

lemma deletion_parts_disjoint (G : SimpleGraph V) (S : Set V) :
    Disjoint (avoid G S).edgeFinset (S.toFinset.biUnion (fun v => G.incidenceFinset v)) := by
  apply Finset.disjoint_left.mpr
  intro e he hI
  obtain ⟨v,hv,heI⟩ := Finset.mem_biUnion.mp hI
  have hvS := Set.mem_toFinset.mp hv
  induction e using Sym2.ind with
  | h x y =>
    have heA : (avoid G S).Adj x y := (avoid G S).mem_edgeFinset.mp he
    have hvxy := (G.mk'_mem_incidenceSet_iff.mp ((G.mem_incidenceFinset _ _).mp heI)).2
    rcases hvxy with rfl | rfl
    · exact heA.2.1 hvS
    · exact heA.2.2 hvS

lemma edge_delete_independent_set (G : SimpleGraph V) (S : Set V)
    (hind : ∀ x ∈ S, ∀ y ∈ S, ¬G.Adj x y) :
    G.edgeSet.ncard = (avoid G S).edgeSet.ncard + ∑ v ∈ S.toFinset, G.degree v := by
  have hd : (S.toFinset : Set V).PairwiseDisjoint (fun v => G.incidenceFinset v) := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro e hex hey
    exact hind x (Set.mem_toFinset.mp hx) y (Set.mem_toFinset.mp hy)
      (G.adj_of_mem_incidenceSet hxy ((G.mem_incidenceFinset _ _).mp hex)
        ((G.mem_incidenceFinset _ _).mp hey))
  have hh := congrArg Finset.card (deletion_edges_partition G S)
  rw [Finset.card_union_of_disjoint (deletion_parts_disjoint G S),Finset.card_biUnion hd] at hh
  simp only [card_incidenceFinset_eq_degree,edgeFinset_card,← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hh
  exact hh

lemma induced_cycle_vertex_delete_exact {G : SimpleGraph V} (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (hind : C.IsInduced)
    (hfour : ∀ v ∈ C.verts, G.degree v = 4) :
    G.edgeSet.ncard = (avoid G C.verts).edgeSet.ncard + 3 * C.verts.ncard := by
  let R := G \ C.spanningCoe
  have heq : avoid R C.verts = avoid G C.verts := by
    ext x y
    constructor
    · rintro ⟨h,hx,hy⟩; exact ⟨h.1,hx,hy⟩
    · rintro ⟨h,hx,hy⟩; exact ⟨⟨h,fun hh => hx (C.edge_vert hh)⟩,hx,hy⟩
  have hiR : ∀ x ∈ C.verts, ∀ y ∈ C.verts, ¬R.Adj x y := by
    intro x hx y hy hxy
    exact hxy.2 (hind hx hy hxy.1)
  have hdeg : ∀ v ∈ C.verts, R.degree v = 2 := by
    intro v hv
    have hd := degree_sdiff_of_le C.spanningCoe_le v
    have hC := CriticalNestedCycles.cycle_degree C hc v
    rw [if_pos hv] at hC
    have hG := hfour v hv
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hC hG ⊢
    change Nat.card (R.neighborSet v) = Nat.card (G.neighborSet v) - Nat.card (C.spanningCoe.neighborSet v) at hd
    omega
  have hsum : (∑ v ∈ C.verts.toFinset, R.degree v) = 2 * C.verts.ncard := by
    calc
      _ = ∑ _v ∈ C.verts.toFinset, 2 := Finset.sum_congr rfl (fun v hv => hdeg v (Set.mem_toFinset.mp hv))
      _ = _ := by simp only [Finset.sum_const,smul_eq_mul,Set.toFinset_card,
        ← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Nat.mul_comm]
  have hb := edge_delete_independent_set R C.verts hiR
  rw [heq] at hb
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hsum hb
  rw [hsum] at hb
  have hcard : R.edgeSet.ncard + C.edgeSet.ncard = G.edgeSet.ncard := by
    dsimp only [R]
    rw [edgeSet_sdiff]
    exact Set.ncard_diff_add_ncard_of_subset C.edgeSet_subset
  rw [regular_two_edge_vertex_card C hc.2] at hcard
  omega

lemma outside_edges_formula {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) :
    (avoid G C.verts).edgeSet.ncard + C.verts.ncard = 2 * (G.support \ C.verts).ncard := by
  have hCsup := CriticalOutsideCycles.cycle_verts_in_support C hc.2
  have he := induced_cycle_vertex_delete_exact C hc hind (fun v hv => hfour v (hCsup hv))
  have hg := CountThreeOrder.four_regular_support_edges hfour
  have hv := Set.ncard_diff_add_ncard_of_subset hCsup
  omega

end Erdos184.CycleOutsideBudget
