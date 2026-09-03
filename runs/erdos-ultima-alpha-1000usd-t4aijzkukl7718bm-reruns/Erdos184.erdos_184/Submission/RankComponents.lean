import Submission.RankCriticalPartitions

/-!
Combining pure-cycle bounds over connected components, with the exact
order-minus-components charge. This supplies a legitimate connected-graph
reduction for the rank-based approach.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace RankComponents
open RankCritical RankCriticalPartitions
variable {V : Type*} [Fintype V]

lemma card_eq_sum_component_card (G : SimpleGraph V) :
    Fintype.card V = ∑ c : G.ConnectedComponent, Fintype.card c := by
  let f : (Σ c : G.ConnectedComponent, c) → V := fun x => x.2.val
  have hi : Function.Injective f := by
    rintro ⟨c,x⟩ ⟨d,y⟩ h
    have hxy : x.val = y.val := h
    have hcd : c = d := ConnectedComponent.eq_of_common_vertex x.property (hxy.symm ▸ y.property)
    subst d
    have hsub : x = y := Subtype.ext hxy
    subst y
    rfl
  have hs : Function.Surjective f := by
    intro v
    exact ⟨⟨G.connectedComponentMk v,⟨v,rfl⟩⟩,rfl⟩
  have hh := Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  rw [Fintype.card_sigma] at hh
  exact hh.symm

lemma rank_eq_sum_component_order (G : SimpleGraph V) :
    graphRank G = ∑ c : G.ConnectedComponent, (Fintype.card c - 1) := by
  have hc : ∀ c : G.ConnectedComponent, (Fintype.card c - 1) + 1 = Fintype.card c := by
    intro c
    have hpos : 0 < Fintype.card c := Fintype.card_pos_iff.mpr c.nonempty_supp.to_subtype
    omega
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset G.ConnectedComponent)) rfl
    (fun c _ => hc c)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hs
  rw [← card_eq_sum_component_card G] at hs
  unfold graphRank
  rw [Nat.card_eq_fintype_card]
  omega

set_option maxHeartbeats 800000 in
lemma combine_component_decompositions (G : SimpleGraph V)
    (D : ∀ c : G.ConnectedComponent, Finset c.toSimpleGraph.Subgraph)
    (hc : ∀ c H, H ∈ D c → H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : ∀ c, IsDecomposition c.toSimpleGraph (D c)) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ ∑ c, (D c).card := by
  let F := fun c : G.ConnectedComponent => (D c).image (Subgraph.map c.toSimpleGraph_hom)
  let E := Finset.univ.biUnion F
  have hF (c : G.ConnectedComponent) (H : c.toSimpleGraph.Subgraph) :
      (H.map c.toSimpleGraph_hom).verts ⊆ c.supp := by
    rintro v ⟨x,hx,rfl⟩
    exact x.property
  refine ⟨E,?_,⟨?_,?_⟩,?_⟩
  · intro K hK
    obtain ⟨c,_,hK⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hK
    have hcy := subgraph_image_cycle_of_injective c.toSimpleGraph_hom Subtype.val_injective H
      (hc c H hH).1 (by
        intro x
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using (hc c H hH).2 x)
    refine ⟨hcy.1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcy.2 x
  · intro J hJ K hK hne
    obtain ⟨c,_,hJ⟩ := Finset.mem_biUnion.mp hJ
    obtain ⟨d,_,hK⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    by_cases hcd : c = d
    · subst d
      have hHL : H ≠ L := fun h => hne (congrArg (Subgraph.map c.toSimpleGraph_hom) h)
      have hdis := (hd c).1 hH hL hHL
      apply Set.disjoint_left.mpr
      intro e heH heL
      simp only [Subgraph.edgeSet_map] at heH heL
      obtain ⟨eH,heH,hEH⟩ := heH
      obtain ⟨eL,heL,hEL⟩ := heL
      have heq : eH = eL := Sym2.map.injective Subtype.val_injective (hEH.trans hEL.symm)
      exact Set.disjoint_left.mp hdis heH (heq.symm ▸ heL)
    · apply Set.disjoint_left.mpr
      intro e heH heL
      induction e using Sym2.ind with
      | h u v =>
        have huH := (H.map c.toSimpleGraph_hom).edge_vert heH
        have huL := (L.map d.toSimpleGraph_hom).edge_vert heL
        exact hcd (ConnectedComponent.eq_of_common_vertex (hF c H huH) (hF d L huL))
  · ext e
    constructor
    · rintro ⟨_,⟨H,rfl⟩,_,⟨hH,rfl⟩,heH⟩
      exact H.edgeSet_subset heH
    · intro he
      induction e using Sym2.ind with
      | h u v =>
        let c := G.connectedComponentMk u
        let x : c := ⟨u,rfl⟩
        let y : c := ⟨v,c.mem_supp_of_adj_mem_supp (show u ∈ c.supp from rfl) he⟩
        have hxy : s(x,y) ∈ c.toSimpleGraph.edgeSet := he
        rw [← (hd c).2] at hxy
        obtain ⟨H,hH,hxy⟩ := Set.mem_iUnion₂.mp hxy
        apply Set.mem_iUnion₂.mpr
        refine ⟨H.map c.toSimpleGraph_hom,?_,?_⟩
        · exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,Finset.mem_image.mpr ⟨H,hH,rfl⟩⟩
        · exact ⟨x,y,hxy,rfl,rfl⟩
  · calc
      E.card ≤ ∑ c, (F c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, (D c).card := Finset.sum_le_sum (fun c _ => Finset.card_image_le)

lemma bound_of_component_bounds (C : ℕ) (G : SimpleGraph V)
    (hb : ∀ c : G.ConnectedComponent, HasBound C c.toSimpleGraph) : HasBound C G := by
  choose D hc hd hcard using hb
  obtain ⟨E,hcE,hdE,hcardE⟩ := combine_component_decompositions G D hc hd
  refine ⟨E,hcE,hdE,hcardE.trans ?_⟩
  have hbound : (∑ c : G.ConnectedComponent, (D c).card) ≤
      ∑ c : G.ConnectedComponent, C * (Fintype.card c - 1) := by
    apply Finset.sum_le_sum
    intro c _
    have hr := connected_rank c.connected_toSimpleGraph
    have heq : graphRank c.toSimpleGraph = Fintype.card c - 1 := by omega
    simpa only [heq] using hcard c
  rw [← Finset.mul_sum,← rank_eq_sum_component_order G] at hbound
  exact hbound

end RankComponents
end Erdos184
