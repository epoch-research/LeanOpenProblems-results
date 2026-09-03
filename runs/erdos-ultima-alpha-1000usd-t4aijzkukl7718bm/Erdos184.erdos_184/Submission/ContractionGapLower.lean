import Submission.ContractionModels

/-! Exact integral and fractional counts for the contraction obstruction.
This is not a disproof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGap
open Critical Rigidity BlockRestriction CycleCertificates
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

lemma degree_bound_of_two_avoiding {V : Type*} [Fintype V] {G : SimpleGraph V}
    (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition G D) (v : V)
    (H K : G.Subgraph) (hH : H ∈ D) (hK : K ∈ D) (hne : H ≠ K)
    (hvH : v ∉ H.verts) (hvK : v ∉ K.verts) :
    G.degree v + 4 ≤ 2 * D.card := by
  let A := D.filter (fun L => v ∈ L.verts)
  have hsub : ({H,K} : Finset G.Subgraph) ⊆ D \ A := by
    intro L hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact Finset.mem_sdiff.mpr ⟨hH,by simpa only [A,Finset.mem_filter,hH,true_and] using hvH⟩
    · have he := Finset.mem_singleton.mp hL
      subst L
      exact Finset.mem_sdiff.mpr ⟨hK,by simpa only [A,Finset.mem_filter,hK,true_and] using hvK⟩
  have hc : 2 ≤ (D \ A).card := by simpa [hne] using Finset.card_le_card hsub
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun L => v ∈ L.verts) D)
  change (D \ A).card + A.card = D.card at hcard
  have hsum := subfamilyGraph_degree D hdec.1 v
  have hg : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  rw [hg] at hsum
  have hdeg (L) (hL : L ∈ D) : L.spanningCoe.degree v = if v ∈ L.verts then 2 else 0 := by
    exact regular_two_spanning_degree L (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using (hD L hL).2) v
  have he : G.degree v = 2 * A.card := by
    rw [hsum]
    calc
      _ = ∑ L ∈ D, if v ∈ L.verts then 2 else 0 := Finset.sum_congr rfl hdeg
      _ = _ := by simp [A,Finset.sum_ite,Nat.mul_comm]
  omega

lemma graph_lower : 5 ≤ number graph := by
  obtain ⟨D,hD,hdec,hc⟩ := minimum_cycles (G := graph) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using graph_even)
  obtain ⟨H,hH,hHL⟩ := leftModel.exists_internal_cycle D (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD) hdec (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using completed_gap 1)
  obtain ⟨K,hK,hKR⟩ := rightModel.exists_internal_cycle D (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD) hdec (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using completed_gap 0)
  have hne : H ≠ K := by
    rintro rfl
    obtain ⟨v⟩ := (hD H hH).1.nonempty
    exact Set.disjoint_left.mp blocks_disjoint (hHL v.property) (hKR v.property)
  have hvH : (1 : Fin 29) ∉ H.verts := fun h => blocks_avoid_one.1 (hHL h)
  have hvK : (1 : Fin 29) ∉ K.verts := fun h => blocks_avoid_one.2 (hKR h)
  have hb := degree_bound_of_two_avoiding D hD hdec 1 H K hH hK hne hvH hvK
  have hd := graph_degree_one
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hb hd
  omega

lemma graph_number : number graph = 5 := Nat.le_antisymm graph_upper graph_lower


#print axioms graph_number
end Erdos184Work.ContractionGap
