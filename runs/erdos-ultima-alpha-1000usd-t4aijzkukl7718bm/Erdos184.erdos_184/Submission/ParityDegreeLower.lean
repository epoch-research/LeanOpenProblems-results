import Submission.OddForestReduction

/-! Degree/parity lower certificates for cycle-and-edge partitions.
No completeness theorem for these certificates is asserted. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.ParityDegreeLower
open Critical
set_option maxHeartbeats 300000
variable {V : Type*} [Fintype V]

lemma independent_degree_sum_le (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) :
    (∑ v ∈ B, G.degree v) ≤ G.edgeFinset.card := by
  have hp : (B : Set V).PairwiseDisjoint (fun v => G.incidenceFinset v) := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro e he hu'
    exact hB u hu v hv (G.adj_of_mem_incidenceSet huv
      ((G.mem_incidenceFinset u e).mp he) ((G.mem_incidenceFinset v e).mp hu'))
  have hs : B.biUnion (fun v => G.incidenceFinset v) ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp he
    exact G.incidenceFinset_subset v hv
  have hc := Finset.card_le_card hs
  rw [Finset.card_biUnion hp] at hc
  simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hc

lemma singleton_degree_pos {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    {v : V} (hv : Odd (G.degree v)) :
    1 ≤ (subfamilyGraph (edgePieces D)).degree v := by
  have hp := edgePieces_degree_parity D hD hdec v
  have hn := Nat.not_even_iff_odd.mpr hv
  have hne := mt hp.mp hn
  rw [Nat.even_iff] at hne
  omega

lemma independent_odd_le_singletons {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (B : Finset V) (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hodd : ∀ v ∈ B, Odd (G.degree v)) : B.card ≤ (edgePieces D).card := by
  let F := subfamilyGraph (edgePieces D)
  have hsum : B.card ≤ ∑ v ∈ B, F.degree v := by
    have hh := Finset.sum_le_sum (s := B) (fun v hv => singleton_degree_pos D hD hdec (hodd v hv))
    simpa only [Finset.sum_const,smul_eq_mul,mul_one] using hh
  have hi := independent_degree_sum_le F B (fun u hu v hv huv =>
    hB u hu v hv (subfamilyGraph_le _ huv))
  have hc := edgePieces_graph_card D hdec
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hi hc
  exact hsum.trans (hi.trans_eq hc)

/-- A degree set A and a disjoint set O of odd vertices give a lower bound
once a lower bound b for the singleton count is known. -/
lemma degree_parity_bound {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (A O : Finset V) (hA : 1 ≤ A.card) (hAO : Disjoint A O)
    (hO : ∀ v ∈ O, Odd (G.degree v)) (b : ℕ) (hb : b ≤ (edgePieces D).card) :
    (∑ v ∈ A, G.degree v) + (2 * A.card - 2) * b + O.card ≤ 2 * A.card * D.card := by
  let E := edgePieces D
  let C := D \ E
  let F := subfamilyGraph E
  let M := subfamilyGraph C
  have hED : E ⊆ D := Finset.filter_subset _ _
  have hCD : C ⊆ D := Finset.sdiff_subset
  have hpE : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hED hH) (hED hK) hne
  have hpC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hdec.1 (hCD hH) (hCD hK) hne
  have hC : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases hD H (hCD hH) with hc | he
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hc
    · exact ((Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hCD hH,he⟩)).elim
  have hFcard : F.edgeFinset.card = E.card := edgePieces_graph_card D hdec
  have hFO : O.card ≤ ∑ v ∈ O, F.degree v := by
    have hh := Finset.sum_le_sum (s := O) (fun v hv => singleton_degree_pos D hD hdec (hO v hv))
    simpa only [Finset.sum_const,smul_eq_mul,mul_one] using hh
  have hFAO : (∑ v ∈ A, F.degree v) + (∑ v ∈ O, F.degree v) ≤ 2 * E.card := by
    have hs := Finset.sum_le_univ_sum_of_nonneg (s := A ∪ O) (fun v => Nat.zero_le (F.degree v))
    rw [Finset.sum_union hAO,F.sum_degrees_eq_twice_card_edges] at hs
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hs hFcard
    omega
  have hMA : (∑ v ∈ A, M.degree v) ≤ 2 * A.card * C.card := by
    have hd : ∀ v : V, M.degree v ≤ 2 * C.card := by
      intro v
      rw [subfamilyGraph_degree C hpC]
      have hh := Finset.sum_le_sum (s := C) (fun H hH => show H.spanningCoe.degree v ≤ 2 by
        rw [regular_two_spanning_degree H (hC H hH).2]
        split_ifs <;> omega)
      simpa only [Finset.sum_const,smul_eq_mul,mul_comm] using hh
    have hs := Finset.sum_le_sum (s := A) (fun v _ => hd v)
    simpa only [Finset.sum_const,smul_eq_mul,← mul_assoc,mul_comm] using hs
  have hDG : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hdegs : ∀ v, M.degree v + F.degree v = G.degree v := by
    intro v
    have h := Finset.sum_sdiff (f := fun H : G.Subgraph => H.spanningCoe.degree v) hED
    change (∑ H ∈ C, H.spanningCoe.degree v) + (∑ H ∈ E, H.spanningCoe.degree v) = _ at h
    rw [← subfamilyGraph_degree C hpC,← subfamilyGraph_degree E hpE,
      ← subfamilyGraph_degree D hdec.1,hDG] at h
    exact h
  have hAeq : (∑ v ∈ A, M.degree v) + (∑ v ∈ A, F.degree v) = ∑ v ∈ A, G.degree v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => hdegs v)
  have hcount : C.card + E.card = D.card := Finset.card_sdiff_add_card_eq_card hED
  have hmul := Nat.mul_le_mul_left (2 * A.card - 2) hb
  have ha' : 2 * A.card - 2 + 2 = 2 * A.card := by omega
  change b ≤ E.card at hb
  change (2 * A.card - 2) * b ≤ (2 * A.card - 2) * E.card at hmul
  nlinarith

/-- Independent odd vertices bound the singleton count; all odd vertices outside
A can additionally contribute to the degree/parity certificate. -/
lemma independent_odd_degree_bound {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D)
    (A B O : Finset V) (hA : 1 ≤ A.card) (hAO : Disjoint A O)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (hoddB : ∀ v ∈ B, Odd (G.degree v)) (hoddO : ∀ v ∈ O, Odd (G.degree v)) :
    (∑ v ∈ A, G.degree v) + (2 * A.card - 2) * B.card + O.card ≤ 2 * A.card * D.card :=
  degree_parity_bound D hD hdec A O hA hAO hoddO B.card
    (independent_odd_le_singletons D hD hdec B hB hoddB)

end Erdos184Work.ParityDegreeLower

#print axioms Erdos184Work.ParityDegreeLower.independent_degree_sum_le
#print axioms Erdos184Work.ParityDegreeLower.degree_parity_bound
#print axioms Erdos184Work.ParityDegreeLower.independent_odd_degree_bound
