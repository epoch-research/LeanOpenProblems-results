import Submission.Cycles

/-!
A limitation of a fundamental-cycle-only approach. A partition into simple
cycles, each using at most one edge outside a prescribed graph R, requires
2 |E(G)| <= 3 |E(R)|. In particular no spanning tree of K5 permits such a
partition. This does not refute partitions whose cycles merely meet the tree,
and does not settle the original conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.FundamentalCycleObstruction
variable {V : Type*} [Fintype V]

/-- Restricting the edge partition to an arbitrary edge set preserves the
sum of the cardinalities. -/
lemma decomposition_restricted_edge_card (G : SimpleGraph V)
    (D : Finset G.Subgraph) (hd : IsDecomposition G D) (S : Set (Sym2 V)) :
    (∑ H ∈ D, (H.edgeSet ∩ S).ncard) = (G.edgeSet ∩ S).ncard := by
  let F := fun H : G.Subgraph => (H.edgeSet ∩ S).toFinset
  have hdis : (D : Set G.Subgraph).PairwiseDisjoint F := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hd.1 hH hK hne)
      (Set.mem_toFinset.mp heH).1 (Set.mem_toFinset.mp heK).1
  have hcov : D.biUnion F = (G.edgeSet ∩ S).toFinset := by
    ext e
    simp only [Finset.mem_biUnion, F, Set.mem_toFinset]
    constructor
    · rintro ⟨H, hH, heH, heS⟩
      exact ⟨H.edgeSet_subset heH, heS⟩
    · rintro ⟨heG, heS⟩
      rw [← hd.2] at heG
      obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp heG
      exact ⟨H, hH, heH, heS⟩
  have hh := Finset.card_biUnion hdis
  rw [hcov] at hh
  simpa only [F, ← Set.ncard_eq_toFinset_card'] using hh.symm

/-- At most one unmarked edge per cycle is a strong density restriction,
not a property supplied by a choice of spanning tree. -/
lemma density_bound_of_at_most_one_unmarked (G R : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hone : ∀ H ∈ D, (H.edgeSet \ R.edgeSet).ncard ≤ 1) :
    2 * G.edgeSet.ncard ≤ 3 * R.edgeSet.ncard := by
  have hu : (G.edgeSet \ R.edgeSet).ncard ≤ D.card := by
    rw [Set.diff_eq, ← decomposition_restricted_edge_card G D hd]
    calc
      (∑ H ∈ D, (H.edgeSet ∩ R.edgeSetᶜ).ncard) ≤ ∑ _H ∈ D, 1 := by
        exact Finset.sum_le_sum (fun H hH => hone H hH)
      _ = D.card := by simp
  have hthree := cycle_decomposition_three_mul_card_le_edges G D hc hd
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hthree
  have hsum := Set.ncard_inter_add_ncard_diff_eq_ncard G.edgeSet R.edgeSet
  have hle := Set.ncard_le_ncard (Set.inter_subset_right (s := G.edgeSet) (t := R.edgeSet))
  omega

/-- A dense enough graph must have a piece using at least two unmarked edges
in every pure-cycle decomposition. -/
lemma exists_two_unmarked_of_dense (G R : SimpleGraph V)
    (hden : 3 * R.edgeSet.ncard < 2 * G.edgeSet.ncard)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ H ∈ D, 2 ≤ (H.edgeSet \ R.edgeSet).ncard := by
  by_contra! hn
  have hb := density_bound_of_at_most_one_unmarked G R D hc hd (by
    intro H hH
    have hh := hn H hH
    omega)
  omega

/-- K5 is already an obstruction for EVERY spanning tree, hence in particular
for DFS trees. The conclusion only forbids fundamental-cycle-only partitions. -/
lemma complete_five_no_fundamental_partition
    (T : SimpleGraph (Fin 5)) (hT : T.IsTree)
    (D : Finset (⊤ : SimpleGraph (Fin 5)).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition ⊤ D) :
    ∃ H ∈ D, 2 ≤ (H.edgeSet \ T.edgeSet).ncard := by
  refine exists_two_unmarked_of_dense ⊤ T ?_ D (fun H hH => ⟨(hc H hH).1, ?_⟩) hd
  swap
  · intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hc H hH).2 v
  have ht := hT.card_edgeFinset
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, Nat.card_fin] at ht
  have hk : (⊤ : SimpleGraph (Fin 5)).edgeSet.ncard = 10 := by
    have hh := card_edgeFinset_top_eq_card_choose_two (V := Fin 5)
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_fin] using hh
  rw [hk]
  omega

end Erdos184.FundamentalCycleObstruction
