import Submission.Cuts
import Submission.RankEvenCuts

/-! Edge-connectivity supplied by spanning cycle packings, and parity
sharpening for finite even graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace HamiltonPackingConnectivity
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma edge_connected_of_spanning_cycle_packing (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdis : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hspan : ∀ H ∈ D, H.verts = Set.univ) : G.IsEdgeConnected (2 * D.card) := by
  intro u v F hF
  have hcard : F.ncard < 2 * D.card := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card'] at hF
    exact_mod_cast hF
  have hex : ∃ H ∈ D, (F ∩ H.edgeSet).ncard < 2 := by
    by_contra! hn
    let B := fun H : G.Subgraph => (F ∩ H.edgeSet).toFinset
    have hbdis : Set.PairwiseDisjoint (D : Set G.Subgraph) B := by
      intro H hH K hK hne
      apply Finset.disjoint_left.mpr
      intro e heH heK
      exact Set.disjoint_left.mp (hdis hH hK hne)
        (Set.mem_toFinset.mp heH).2 (Set.mem_toFinset.mp heK).2
    have hle : 2 * D.card ≤ ∑ H ∈ D, (B H).card := by
      calc
        _ = ∑ _H ∈ D, 2 := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun H hH => by
          simpa only [B,← Set.ncard_eq_toFinset_card'] using hn H hH)
    rw [← Finset.card_biUnion hbdis] at hle
    have hsub : D.biUnion B ⊆ F.toFinset := by
      intro e he
      obtain ⟨H,_,heH⟩ := Finset.mem_biUnion.mp he
      exact Set.mem_toFinset.mpr (Set.mem_toFinset.mp heH).1
    have hh := Finset.card_le_card hsub
    rw [← Set.ncard_eq_toFinset_card'] at hh
    omega
  obtain ⟨H,hH,hh⟩ := hex
  have hhc := coe_connected_spanning_of_verts_univ H (hc H hH).1 (hspan H hH)
  have hhr := coe_regular_spanning_of_verts_univ H (hc H hH).2 (hspan H hH)
  have htwo := regular_two_isEdgeConnected H.spanningCoe hhc hhr
  have hens : (F ∩ H.edgeSet).encard < 2 := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card']
    exact_mod_cast hh
  have hr := htwo u v hens
  apply hr.mono
  intro a b hab
  obtain ⟨hab,hn⟩ := SimpleGraph.deleteEdges_adj.mp hab
  exact SimpleGraph.deleteEdges_adj.mpr ⟨H.adj_sub hab,fun hF => hn ⟨hF,hab⟩⟩

lemma deletion_edge_connected (G : SimpleGraph V) (k l : ℕ)
    (hG : G.IsEdgeConnected (k+l)) (F : Set (Sym2 V)) (hF : F.ncard ≤ l) :
    (G.deleteEdges F).IsEdgeConnected k := by
  intro u v S hS
  have hs : S.ncard < k := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card'] at hS
    exact_mod_cast hS
  have hu : (F ∪ S).ncard < k+l := (Set.ncard_union_le F S).trans_lt (by omega)
  have hue : (F ∪ S).encard < k+l := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card']
    exact_mod_cast hu
  have hr := hG u v hue
  simpa only [SimpleGraph.deleteEdges_deleteEdges] using hr

lemma even_edge_connected_succ (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (k : ℕ) (hk : Odd k)
    (hG : G.IsEdgeConnected k) : G.IsEdgeConnected (k+1) := by
  intro u v F hF
  by_contra hn
  let R := G.deleteEdges F
  let f : V → Bool := fun x => decide (R.Reachable u x)
  let A := RankCriticalPartitions.monochromatic G f
  let S := G.edgeSet \ A.edgeSet
  have hsub : S ⊆ F := by
    intro e heS
    induction e using Sym2.ind with
    | h a b =>
      by_contra hf
      have hab : R.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨heS.1,hf⟩
      have heq : R.Reachable u a ↔ R.Reachable u b :=
        ⟨fun h => h.trans hab.reachable,fun h => h.trans hab.symm.reachable⟩
      apply heS.2
      refine ⟨heS.1,?_⟩
      change decide (R.Reachable u a) = decide (R.Reachable u b)
      simp only [heq]
  have hsmall : F.ncard ≤ k := by
    have hh : F.ncard < k+1 := by
      rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card'] at hF
      exact_mod_cast hF
    omega
  have hs := (Set.ncard_le_ncard hsub).trans hsmall
  have hseven : Even S.ncard := RankEvenCuts.even_two_color_cut G he f
  obtain ⟨a,ha⟩ := hseven
  obtain ⟨b,hb⟩ := hk
  have hlt : S.ncard < k := by omega
  have henc : S.encard < k := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card']
    exact_mod_cast hlt
  have hr := hG u v henc
  have hle : G.deleteEdges S ≤ A := by
    intro a b hab
    obtain ⟨hab,hnab⟩ := SimpleGraph.deleteEdges_adj.mp hab
    by_contra hnot
    exact hnab ⟨hab,hnot⟩
  have hc := RankCriticalPartitions.color_eq_of_reachable G f (hr.mono hle)
  have hself : R.Reachable u u := .refl u
  change ¬R.Reachable u v at hn
  change decide (R.Reachable u u) = decide (R.Reachable u v) at hc
  simp only [hself,hn,decide_true,decide_false] at hc
  cases hc

end HamiltonPackingConnectivity
end Erdos184
