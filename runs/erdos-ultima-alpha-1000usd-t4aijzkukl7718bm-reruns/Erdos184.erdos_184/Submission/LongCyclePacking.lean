import Submission.Circumference

/-! Long-cycle packing phases. These are not a uniform linear bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma exists_maximal_long_cycle_packing {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 ∧ k < H.edgeSet.ncard) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      ∀ u (p : (G \ unionPieces G D).Walk u u), p.IsCycle → p.length ≤ k := by
  let P (D : Finset G.Subgraph) : Prop :=
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 ∧ k < H.edgeSet.ncard) ∧
    Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)
  have hP0 : P ∅ := by simp [P]
  obtain ⟨D, hD, hm⟩ := (Set.toFinite {D | P D}).exists_maximal ⟨∅, hP0⟩
  refine ⟨D, hD.1, hD.2, ?_⟩
  intro u p hp
  by_contra! hlen
  let A := G \ unionPieces G D
  have hAG : A ≤ G := sdiff_le
  let H : G.Subgraph := promote hAG p.toSubgraph
  have hc0 := cycle_subgraph_regular A hp
  have hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    refine ⟨hc0.1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hc0.2 v
  have hcard : H.edgeSet.ncard = p.length := by
    have hh := trail_spanning_edge_card p hp.isTrail
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] at hh
    exact hh
  have hdis : ∀ K ∈ D, Disjoint H.edgeSet K.edgeSet := by
    intro K hK
    apply Set.disjoint_left.mpr
    intro e heH heK
    have heA : e ∈ A.edgeSet := p.toSubgraph.edgeSet_subset heH
    change e ∈ (G \ unionPieces G D).edgeSet at heA
    rw [SimpleGraph.edgeSet_sdiff] at heA
    apply heA.2
    rw [unionPieces_edgeSet]
    simp only [Set.mem_iUnion]
    exact ⟨K, hK, heK⟩
  have hnot : H ∉ D := by
    intro hH
    obtain ⟨e, he⟩ := cycle_edgeSet_nonempty H hcH.1 hcH.2
    exact Set.disjoint_left.mp (hdis H hH) he he
  have hPD : P (insert H D) := by
    constructor
    · intro K hK
      rcases Finset.mem_insert.mp hK with rfl | hK
      · exact ⟨hcH.1, hcH.2, hcard.symm ▸ hlen⟩
      · exact hD.1 K hK
    · rw [Finset.coe_insert]
      exact hD.2.insert (fun K hK _ => hdis K hK)
  have hsub : insert H D ⊆ D := hm hPD (Finset.subset_insert _ _)
  exact hnot (hsub (Finset.mem_insert_self _ _))

/-- Removing an edge-disjoint cycle family from an even graph leaves an even graph. -/
lemma even_residual_of_cycle_packing {V : Type*} [Fintype V]
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    ∀ v, Even ((G \ unionPieces G D).degree v) := by
  intro v
  have hU : Even ((unionPieces G D).degree v) := by
    have hh := unionPieces_degree G D hd v
    have hs : Even (∑ H ∈ D, H.degree v) :=
      Finset.even_sum _ (fun H hH => regular_two_piece_degree_even H (hc H hH).2 v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
    rwa [hh]
  have heG := he v
  have heq := degree_sdiff_of_le (unionPieces_le G D) v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hU heG heq ⊢
  rw [heq]
  obtain ⟨a, ha⟩ := heG
  obtain ⟨b, hb⟩ := hU
  exact ⟨a - b, by omega⟩

lemma cycle_packing_edge_card_partition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    (∑ H ∈ D, H.edgeSet.ncard) + (G \ unionPieces G D).edgeFinset.card =
      G.edgeFinset.card := by
  have hsub : (unionPieces G D).edgeFinset ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.edgeSet_mono (unionPieces_le G D) (SimpleGraph.mem_edgeFinset.mp he))
  have hh := unionPieces_edge_card G D hd
  rw [← hh, SimpleGraph.edgeFinset_sdiff]
  simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hsub

/-- One packing phase leaves at most `(k-1)n` edges. Each selected cycle
pays for at least `k+1` edges, giving a separate bound on the phase cost. -/
lemma long_cycle_packing_phase {V : Type*} [Fintype V]
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (k : ℕ) (hk : 2 ≤ k) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ v, Even ((G \ unionPieces G D).degree v)) ∧
      (G \ unionPieces G D).edgeFinset.card ≤ (k - 1) * Fintype.card V ∧
      (k + 1) * D.card + (G \ unionPieces G D).edgeFinset.card ≤ G.edgeFinset.card := by
  obtain ⟨D, hcD, hdD, hrem⟩ := exists_maximal_long_cycle_packing G k
  have hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => ⟨(hcD H hH).1, (hcD H hH).2.1⟩
  refine ⟨D, hc, hdD, even_residual_of_cycle_packing G he D hc hdD,
    (by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
        using edge_card_le_of_cycle_length_bound _ k hk hrem), ?_⟩
  have hs : (k + 1) * D.card ≤ ∑ H ∈ D, H.edgeSet.ncard := by
    calc
      (k + 1) * D.card = ∑ H ∈ D, (k + 1) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun H hH => (hcD H hH).2.2)
  have hh := cycle_packing_edge_card_partition G D hdD
  omega

lemma complete_cycle_packing {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (F : Finset (G \ unionPieces G D).Subgraph)
    (hcF : ∀ H ∈ F, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdF : IsDecomposition (G \ unionPieces G D) F) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card + F.card := by
  let hAG : G \ unionPieces G D ≤ G := sdiff_le
  let E := D ∪ F.image (promote hAG)
  have hdis : ∀ H ∈ D, ∀ K ∈ F, Disjoint H.edgeSet K.edgeSet := by
    intro H hH K _
    apply Set.disjoint_left.mpr
    intro e heH heK
    have heA := K.edgeSet_subset heK
    rw [SimpleGraph.edgeSet_sdiff] at heA
    apply heA.2
    rw [unionPieces_edgeSet]
    simp only [Set.mem_iUnion]
    exact ⟨H, hH, heH⟩
  refine ⟨E, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · exact hc H hH
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hcF K hK).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcF K hK).2 v
  · intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · exact hd hH hK hne
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hK
      exact hdis H hH X hX
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      exact (hdis K hK X hX).symm
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hdF.1 hX hY (fun h => hne (congrArg (promote hAG) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, _, he⟩
      exact H.edgeSet_subset he
    · intro heG
      by_cases heU : e ∈ (unionPieces G D).edgeSet
      · rw [unionPieces_edgeSet] at heU
        simp only [Set.mem_iUnion] at heU
        obtain ⟨H, hH, heH⟩ := heU
        exact ⟨H, Finset.mem_union_left _ hH, heH⟩
      · have heA : e ∈ (G \ unionPieces G D).edgeSet := by
          rw [SimpleGraph.edgeSet_sdiff]
          exact ⟨heG, heU⟩
        rw [← hdF.2] at heA
        simp only [Set.mem_iUnion] at heA
        obtain ⟨H, hH, heH⟩ := heA
        exact ⟨promote hAG H,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), heH⟩
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)

/-- A dyadic density bound. The number of phases is the exponent `t`, so
this estimate is logarithmic, rather than uniformly linear, in the density. -/
lemma even_cycle_decomposition_dyadic_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (t : ℕ)
    (hm : G.edgeFinset.card ≤ 2 ^ t * Fintype.card V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ (2 * t + 1) * Fintype.card V := by
  induction t generalizing G with
  | zero =>
    obtain ⟨D, hcD, hdD⟩ := even_cycle_decomposition G he
    refine ⟨D, hcD, hdD, ?_⟩
    have hb := cycle_decomposition_card_le_edges G D hcD hdD
    simpa only [pow_zero, one_mul, mul_zero, zero_add] using hb.trans hm
  | succ t ih =>
    have hpow : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by omega)
    obtain ⟨D, hcD, hdD, heA, hsmall, hcost⟩ :=
      long_cycle_packing_phase G he (2 ^ t + 1) (by omega)
    let A := G \ unionPieces G D
    have hA : A.edgeFinset.card ≤ 2 ^ t * Fintype.card V := by
      simpa only [Nat.add_sub_cancel, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
        using hsmall
    obtain ⟨F, hcF, hdF, hbF⟩ := ih A (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using heA) (by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hA)
    have hbD : D.card ≤ 2 * Fintype.card V := by
      have hh : (2 ^ t + 1 + 1) * D.card ≤
          (2 ^ t + 1 + 1) * (2 * Fintype.card V) := by
        have hm' := hm
        simp only [pow_succ] at hm'
        nlinarith
      exact Nat.le_of_mul_le_mul_left hh (by omega)
    obtain ⟨E, hcE, hdE, hbE⟩ := complete_cycle_packing G D hcD hdD F (by
      intro H hH
      refine ⟨(hcF H hH).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcF H hH).2 v) hdF
    refine ⟨E, hcE, hdE, ?_⟩
    nlinarith

lemma even_cycle_decomposition_logarithmic_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      D.card ≤ (2 * Nat.clog 2 (Fintype.card V) + 1) * Fintype.card V := by
  apply even_cycle_decomposition_dyadic_bound G he
  calc
    G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
    _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
    _ = Fintype.card V * Fintype.card V := by ring
    _ ≤ 2 ^ Nat.clog 2 (Fintype.card V) * Fintype.card V :=
      Nat.mul_le_mul_right _ (Nat.le_pow_clog (by omega) _)

/-- An unconditional logarithmic upper bound for arbitrary finite graphs.
The `Nat.clog` factor remains, so this does not establish Erdős 184. -/
lemma cycle_edge_decomposition_logarithmic_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ (2 * Nat.clog 2 (Fintype.card V) + 2) * Fintype.card V := by
  obtain ⟨s, hs, heven⟩ := parity_correction G
  let A := G.deleteEdges (s : Set (Sym2 V))
  let B := G \ A
  have hA : A ≤ G := G.deleteEdges_le _
  have hB : B ≤ G := sdiff_le
  have hab : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint A.edgeSet (G \ A).edgeSet
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    change A.edgeSet ∪ (G \ A).edgeSet = G.edgeSet
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono hA)
  have hbcard : B.edgeFinset.card ≤ s.card := by
    apply Finset.card_le_card
    intro e he
    have he' : e ∈ B.edgeSet := by simpa using he
    simp only [B, A, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_diff, Finset.mem_coe] at he'
    by_contra h
    exact he'.2 ⟨he'.1, h⟩
  obtain ⟨DA, hcA, hdA, hbA⟩ := even_cycle_decomposition_logarithmic_bound A (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heven)
  obtain ⟨DB, hcB, hdB, hbB⟩ := edge_decomposition B
  obtain ⟨D, hcD, hdD, hbD⟩ := combine_decompositions hA hB hab hcover DA DB (by
    intro H hH
    refine Or.inl ⟨(hcA H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcA H hH).2 v) hcB hdA hdB
  refine ⟨D, hcD, hdD, ?_⟩
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hbcard hbB
  nlinarith

/-- The explicit bound just obtained is not itself `O(n)`. This does not
rule out a smaller bound, and is not a disproof of the conjecture. -/
lemma logarithmic_bound_function_not_linear :
    ¬ ((fun n : ℕ => ((2 * Nat.clog 2 n + 2 : ℕ) : ℝ) * (n : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ))) := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbound.bound
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hlarge : N ≤ 2 ^ (N + k) :=
    (Nat.le_add_right N k).trans (Nat.lt_two_pow_self.le)
  have hb := hN (2 ^ (N + k)) hlarge
  simp only [Real.norm_eq_abs, abs_mul, Nat.abs_cast,
    Nat.clog_pow 2 (N + k) (by omega)] at hb
  have hp : (0 : ℝ) < (2 ^ (N + k) : ℕ) := by positivity
  have hcoef := (mul_le_mul_iff_left₀ hp).mp hb
  push_cast at hcoef
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

end Erdos184
