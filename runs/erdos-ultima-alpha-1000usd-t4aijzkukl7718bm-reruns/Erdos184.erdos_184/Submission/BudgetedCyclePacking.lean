import Submission.LongCyclePacking

/-!
Cycle packings maximizing covered edges under a prescribed cardinality budget.
The exchange and residual-density bounds here are unconditional, but do not
supply an O(n)-edge residual for an O(n)-cycle budget.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.BudgetedCyclePacking
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Feasibility for the budgeted packing problem. -/
def Feasible (G : SimpleGraph V) (k : ℕ) (D : Finset G.Subgraph) : Prop :=
  (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧ D.card ≤ k

/-- Covered edge count, expressed as a sum for easy exchange calculations. -/
noncomputable def weight (D : Finset G.Subgraph) : ℕ := ∑ H ∈ D, H.edgeSet.ncard

/-- Global, not just inclusion, optimality. -/
def Optimal (G : SimpleGraph V) (k : ℕ) (D : Finset G.Subgraph) : Prop :=
  Feasible G k D ∧ ∀ E : Finset G.Subgraph, Feasible G k E → weight E ≤ weight D

lemma exists_optimal (G : SimpleGraph V) (k : ℕ) :
    ∃ D : Finset G.Subgraph, Optimal G k D := by
  let S := (Finset.univ : Finset (Finset G.Subgraph)).filter (Feasible G k)
  have hs : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [Feasible]
  obtain ⟨D, hD, hm⟩ := S.exists_max_image weight hs
  refine ⟨D, (Finset.mem_filter.mp hD).2, ?_⟩
  intro E hE
  exact hm E (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩)

/-- A cycle of the residual, promoted to the original graph, is disjoint
from every selected piece. -/
lemma residual_cycle_data (D : Finset G.Subgraph) {u : V}
    (p : (G \ unionPieces G D).Walk u u) (hp : p.IsCycle) :
    ∃ K : G.Subgraph,
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      K.edgeSet.ncard = p.length ∧ K ∉ D ∧
      ∀ H ∈ D, Disjoint K.edgeSet H.edgeSet := by
  let A := G \ unionPieces G D
  let hAG : A ≤ G := sdiff_le
  let K : G.Subgraph := promote hAG p.toSubgraph
  have hc0 := cycle_subgraph_regular A hp
  have hc : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    refine ⟨hc0.1, ?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hc0.2 v
  have hlen : K.edgeSet.ncard = p.length := by
    have hh := trail_spanning_edge_card p hp.isTrail
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hh
  have hdis : ∀ H ∈ D, Disjoint K.edgeSet H.edgeSet := by
    intro H hH
    apply Set.disjoint_left.mpr
    intro e heK heH
    have heA : e ∈ A.edgeSet := p.toSubgraph.edgeSet_subset heK
    change e ∈ (G \ unionPieces G D).edgeSet at heA
    rw [SimpleGraph.edgeSet_sdiff] at heA
    apply heA.2
    rw [unionPieces_edgeSet]
    exact Set.mem_iUnion₂.mpr ⟨H, hH, heH⟩
  have hn : K ∉ D := by
    intro hK
    obtain ⟨e, he⟩ := cycle_edgeSet_nonempty K hc.1 hc.2
    exact Set.disjoint_left.mp (hdis K hK) he he
  exact ⟨K, hc, hlen, hn, hdis⟩

/-- Any unselected disjoint cycle is no larger than any selected member of
an optimal packing: exchange the two pieces, keeping the budget unchanged. -/
lemma Optimal.exchange_le {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (H : G.Subgraph) (hH : H ∈ D)
    (K : G.Subgraph) (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hn : K ∉ D) (hdis : ∀ J ∈ D, Disjoint K.edgeSet J.edgeSet) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  let E := insert K (D.erase H)
  have hnE : K ∉ D.erase H := fun hh => hn (Finset.mem_of_mem_erase hh)
  have hE : Feasible G k E := by
    refine ⟨?_, ?_, ?_⟩
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact hcK
      · exact hm.1.1 J (Finset.mem_of_mem_erase hJ)
    · have her : Set.PairwiseDisjoint (D.erase H : Set G.Subgraph) (fun J => J.edgeSet) := by
        intro J hJ L hL hne
        exact hm.1.2.1 (Finset.mem_of_mem_erase hJ) (Finset.mem_of_mem_erase hL) hne
      rw [show (E : Set G.Subgraph) = insert K (D.erase H : Set G.Subgraph) by
        exact Finset.coe_insert K (D.erase H)]
      exact her.insert (fun J hJ _ => hdis J (Finset.mem_of_mem_erase hJ))
    · have hh := hm.1.2.2
      have hp : 0 < D.card := Finset.card_pos.mpr ⟨H, hH⟩
      dsimp [E]
      rw [Finset.card_insert_of_notMem hnE, Finset.card_erase_of_mem hH]
      omega
  have hmax := hm.2 E hE
  have hsum : weight (D.erase H) + H.edgeSet.ncard = weight D := by
    exact Finset.sum_erase_add _ _ hH
  have hwe : weight E = K.edgeSet.ncard + weight (D.erase H) := by
    exact Finset.sum_insert hnE
  rw [hwe] at hmax
  omega

lemma Optimal.residual_cycle_le {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (H : G.Subgraph) (hH : H ∈ D) {u : V}
    (p : (G \ unionPieces G D).Walk u u) (hp : p.IsCycle) :
    p.length ≤ H.edgeSet.ncard := by
  obtain ⟨K, hcK, hlen, hn, hdis⟩ := residual_cycle_data D p hp
  rw [← hlen]
  exact hm.exchange_le H hH K hcK hn hdis

/-- Unused budget forces the entire residual to be acyclic, not just to
have bounded circumference. -/
lemma Optimal.residual_acyclic_of_lt {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (hlt : D.card < k) :
    (G \ unionPieces G D).IsAcyclic := by
  intro u p hp
  obtain ⟨K, hcK, hlen, hn, hdis⟩ := residual_cycle_data D p hp
  have hE : Feasible G k (insert K D) := by
    refine ⟨?_, ?_, ?_⟩
    · intro H hH
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact hcK
      · exact hm.1.1 H hH
    · rw [Finset.coe_insert]
      exact hm.1.2.1.insert (fun H hH _ => hdis H hH)
    · rw [Finset.card_insert_of_notMem hn]
      omega
  have hh := hm.2 (insert K D) hE
  have heq : weight (insert K D) = K.edgeSet.ncard + weight D := Finset.sum_insert hn
  rw [heq, hlen] at hh
  have hpos := hp.three_le_length
  omega

/-- For an even graph, unused budget means complete coverage. -/
lemma Optimal.residual_eq_bot_of_lt {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (he : ∀ v, Even (G.degree v)) (hlt : D.card < k) :
    G \ unionPieces G D = ⊥ := by
  apply even_acyclic_eq_bot _
  · intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G he D hm.1.1 hm.1.2.1 v
  · exact hm.residual_acyclic_of_lt hlt

/-- The shortest selected cycle controls the residual density. -/
lemma Optimal.residual_density_le_piece {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (H : G.Subgraph) (hH : H ∈ D) :
    (G \ unionPieces G D).edgeSet.ncard ≤
      (H.edgeSet.ncard - 1) * Fintype.card V := by
  have hthree := cycle_edgeSet_three_le H (hm.1.1 H hH).1 (hm.1.1 H hH).2
  have hh := edge_card_le_of_cycle_length_bound (G \ unionPieces G D)
    H.edgeSet.ncard (by omega) (fun u p hp => hm.residual_cycle_le H hH p hp)
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using hh

/-- The global optimum obeys a quantitative density-reduction estimate.
With k=C*n this gives only r<=m/(C+1), not r=O(n). -/
theorem Optimal.residual_density_bound {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (he : ∀ v, Even (G.degree v)) :
    (k + Fintype.card V) * (G \ unionPieces G D).edgeSet.ncard ≤
      Fintype.card V * G.edgeSet.ncard := by
  have hpart := cycle_packing_edge_card_partition G D hm.1.2.1
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hpart
  change weight D + (G \ unionPieces G D).edgeSet.ncard = G.edgeSet.ncard at hpart
  by_cases hfull : D.card = k
  · by_cases hne : D.Nonempty
    · obtain ⟨H, hH, hmin⟩ := D.exists_min_image (fun H => H.edgeSet.ncard) hne
      have hr := hm.residual_density_le_piece H hH
      have hlen : k * H.edgeSet.ncard ≤ weight D := by
        rw [← hfull]
        calc
          D.card * H.edgeSet.ncard = ∑ _J ∈ D, H.edgeSet.ncard := by simp
          _ ≤ weight D := Finset.sum_le_sum (fun J hJ => hmin J hJ)
      have hr' : (G \ unionPieces G D).edgeSet.ncard ≤
          H.edgeSet.ncard * Fintype.card V :=
        hr.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      have hmul := Nat.mul_le_mul_left k hr'
      have hmul' := Nat.mul_le_mul_left (Fintype.card V) hlen
      nlinarith
    · have hz : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hk : k = 0 := by simpa [hz] using hfull.symm
      have hw : weight D = 0 := by simp [weight, hz]
      rw [hw, zero_add] at hpart
      rw [hk, zero_add, hpart]
  · have hlt : D.card < k := lt_of_le_of_ne hm.1.2.2 hfull
    rw [hm.residual_eq_bot_of_lt he hlt]
    simp

/-- The preceding estimate is attained by a genuinely optimal feasible
packing, with no parity or optimality assumptions hidden in the conclusion. -/
theorem exists_budgeted_packing (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (k : ℕ) :
    ∃ D : Finset G.Subgraph,
      Feasible G k D ∧
      (k + Fintype.card V) * (G \ unionPieces G D).edgeSet.ncard ≤
        Fintype.card V * G.edgeSet.ncard := by
  obtain ⟨D, hD⟩ := exists_optimal G k
  exact ⟨D, hD.1, hD.residual_density_bound he⟩

/-- A near-cover completes to a pure-cycle decomposition at the exact
three-edges-per-residual-cycle budget. The residual edge count is an explicit
term; this theorem does not bound it by O(n). -/
lemma complete_near_cover (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (k : ℕ) (D : Finset G.Subgraph) (hD : Feasible G k D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧
      3 * E.card ≤ 3 * k + (G \ unionPieces G D).edgeSet.ncard := by
  have heR := even_residual_of_cycle_packing G he D hD.1 hD.2.1
  obtain ⟨F, hcF, hdF⟩ := even_cycle_decomposition (G \ unionPieces G D) (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using heR v)
  have hcardF := cycle_decomposition_three_mul_card_le_edges
    (G \ unionPieces G D) F (by
      intro H hH
      refine ⟨(hcF H hH).1, ?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcF H hH).2 v) hdF
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hcardF
  obtain ⟨E, hcE, hdE, hbE⟩ := complete_cycle_packing G D hD.1 hD.2.1 F (by
    intro H hH
    refine ⟨(hcF H hH).1, ?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF H hH).2 v) hdF
  refine ⟨E, hcE, hdE, ?_⟩
  have hk := hD.2.2
  omega

end Erdos184.BudgetedCyclePacking
