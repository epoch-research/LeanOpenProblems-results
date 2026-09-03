import Submission.Cycles

/-! Conditional one-vertex-sum reduction for the weighted-cycle approach.
The atomic weighted hypothesis below is not proved here. -/

open SimpleGraph Filter
open scoped Classical
namespace Erdos184

/-- An even separation with at most one shared nonisolated vertex. -/
def HasEvenOneVertexSplit {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ A B : SimpleGraph V,
    A ≤ G ∧ B ≤ G ∧ A ≠ ⊥ ∧ B ≠ ⊥ ∧
    (∀ v, Even (A.degree v)) ∧ (∀ v, Even (B.degree v)) ∧
    Disjoint A.edgeSet B.edgeSet ∧ A.edgeSet ∪ B.edgeSet = G.edgeSet ∧
    (A.support ∩ B.support).ncard ≤ 1

lemma support_card_two_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hne : G ≠ ⊥) : 2 ≤ G.support.ncard := by
  have hex : ∃ u v, G.Adj u v := by
    by_contra! h
    exact hne (SimpleGraph.eq_bot_iff_forall_not_adj.mpr h)
  obtain ⟨u, v, huv⟩ := hex
  have hs : ({u, v} : Set V) ⊆ G.support := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨v, huv⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨u, huv.symm⟩
  simpa [huv.ne] using Set.ncard_le_ncard hs

lemma support_union_of_edge_cover {V : Type*} {G A B : SimpleGraph V}
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet) :
    A.support ∪ B.support = G.support := by
  ext v
  simp only [Set.mem_union, SimpleGraph.mem_support]
  constructor
  · rintro (⟨w, hw⟩ | ⟨w, hw⟩)
    · refine ⟨w, ?_⟩
      change s(v, w) ∈ G.edgeSet
      rw [← hcover]
      exact Or.inl hw
    · refine ⟨w, ?_⟩
      change s(v, w) ∈ G.edgeSet
      rw [← hcover]
      exact Or.inr hw
  · rintro ⟨w, hw⟩
    have hh : s(v, w) ∈ A.edgeSet ∪ B.edgeSet := hcover.symm ▸ hw
    rcases hh with ha | hb
    · exact Or.inl ⟨w, ha⟩
    · exact Or.inr ⟨w, hb⟩

lemma edge_card_lt_of_disjoint_nonempty {V : Type*} [Fintype V]
    {G A B : SimpleGraph V} (hA : A ≤ G) (hB : B ≤ G)
    (hBne : B ≠ ⊥) (hab : Disjoint A.edgeSet B.edgeSet) :
    A.edgeFinset.card < G.edgeFinset.card := by
  have hb : B.edgeSet.Nonempty := by
    by_contra h
    have he : B.edgeSet = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    exact hBne (SimpleGraph.edgeSet_injective (by simpa using he))
  obtain ⟨e, he⟩ := hb
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hA
      (SimpleGraph.mem_edgeFinset.mp he))
  · intro heq
    have heG : e ∈ G.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hB he)
    have heA : e ∈ A.edgeFinset := heq.symm ▸ heG
    exact Set.disjoint_left.mp hab (SimpleGraph.mem_edgeFinset.mp heA) he

lemma support_weight_identity {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : Finset G.Subgraph)
    (hcy : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    2 * ∑ H ∈ D, cycleWeight G H = (G.support.ncard : ℝ) := by
  have heq : (Finset.univ.filter (fun v : V => G.degree v ≠ 0)) =
      G.support.toFinset := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      ← SimpleGraph.degree_pos_iff_mem_support, Nat.pos_iff_ne_zero]
  rw [Set.ncard_eq_toFinset_card' G.support, ← heq]
  exact cycle_weight_total G D hcy hd

universe u

lemma even_bound_of_atomic_bound (ε : ℝ) (hε : 0 ≤ ε)
    (hatom : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) → ¬ HasEvenOneVertexSplit G →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        ε * (D.card : ℝ) ≤ (G.support.ncard : ℝ) - 1) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        ε * (D.card : ℝ) ≤ (G.support.ncard : ℝ) - 1 := by
  intro V _ _ G hne heven
  generalize hn : G.edgeFinset.card = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hs : HasEvenOneVertexSplit G
    · obtain ⟨A, B, hA, hB, hAne, hBne, haeven, hbeven, hab, hcover, hover⟩ := hs
      have hltA := edge_card_lt_of_disjoint_nonempty hA hB hBne hab
      have hltB := edge_card_lt_of_disjoint_nonempty hB hA hAne hab.symm
      obtain ⟨DA, hca, hda, hboundA⟩ := ih A.edgeFinset.card (by omega) A hAne
        (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using haeven)
        (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card])
      obtain ⟨DB, hcb, hdb, hboundB⟩ := ih B.edgeFinset.card (by omega) B hBne
        (by simpa only [← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hbeven)
        (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card])
      obtain ⟨D, hc, hd, hcard⟩ :=
        combine_decompositions hA hB hab hcover DA DB hca hcb hda hdb
      refine ⟨D, hc, hd, ?_⟩
      have hcount : A.support.ncard + B.support.ncard ≤ G.support.ncard + 1 := by
        have hh := Set.ncard_union_add_ncard_inter A.support B.support
        rw [support_union_of_edge_cover hcover] at hh
        omega
      have hcount' : (A.support.ncard : ℝ) + B.support.ncard ≤ G.support.ncard + 1 := by
        exact_mod_cast hcount
      have hcard' : (D.card : ℝ) ≤ (DA.card : ℝ) + DB.card := by exact_mod_cast hcard
      have hm := mul_le_mul_of_nonneg_left hcard' hε
      nlinarith
    · exact hatom G hne heven hs

lemma atomic_bound_of_weight_lower (ε : ℝ)
    (hatom : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) → ¬ HasEvenOneVertexSplit G →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (∀ H ∈ D, ε ≤ cycleWeight G H)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) → ¬ HasEvenOneVertexSplit G →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        ε * (D.card : ℝ) ≤ (G.support.ncard : ℝ) - 1 := by
  intro V _ _ G hne heven hs
  obtain ⟨D, hcy, hd, hw⟩ := hatom G hne heven hs
  refine ⟨D, ?_, hd, ?_⟩
  · intro H hH
    refine Or.inl ⟨(hcy H hH).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcy H hH).2 v
  · have hsum : ε * (D.card : ℝ) ≤ ∑ H ∈ D, cycleWeight G H := by
      calc
        ε * (D.card : ℝ) = ∑ _H ∈ D, ε := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum hw
    have htotal := support_weight_identity G D hcy hd
    have htwo : (2 : ℝ) ≤ G.support.ncard := by exact_mod_cast support_card_two_le G hne
    linarith

lemma weighted_atomic_suffices (ε : ℝ) (hε : 0 < ε)
    (hatom : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G ≠ ⊥ → (∀ v, Even (G.degree v)) → ¬ HasEvenOneVertexSplit G →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (∀ H ∈ D, ε ≤ cycleWeight G H)) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨ε⁻¹, ?_⟩
  intro V _ _ G heven
  by_cases hbot : G = ⊥
  · subst G
    refine ⟨∅, by simp, by simp [IsDecomposition], ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨D, hc, hd, hb⟩ := even_bound_of_atomic_bound ε hε.le
      (atomic_bound_of_weight_lower ε hatom) G hbot heven
    refine ⟨D, hc, hd, ?_⟩
    have hs : (G.support.ncard : ℝ) ≤ Fintype.card V := by
      have hs' := Set.ncard_le_ncard (Set.subset_univ G.support)
      simpa using (show (G.support.ncard : ℝ) ≤ (Set.univ : Set V).ncard by
        exact_mod_cast hs')
    have hb' : ε * (D.card : ℝ) ≤ Fintype.card V := by linarith
    have hh : (D.card : ℝ) ≤ (Fintype.card V : ℝ) / ε := by
      apply (le_div_iff₀ hε).mpr
      linarith
    simpa only [div_eq_mul_inv, mul_comm] using hh

lemma degree_eq_of_other_unsupported {V : Type*} [Fintype V]
    {G A B : SimpleGraph V} (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (v : V) (hv : v ∉ B.support) : A.degree v = G.degree v := by
  have hn : A.neighborSet v = G.neighborSet v := by
    ext w
    change A.Adj v w ↔ G.Adj v w
    have hh : G.Adj v w ↔ A.Adj v w ∨ B.Adj v w := by
      change s(v, w) ∈ G.edgeSet ↔ s(v, w) ∈ A.edgeSet ∪ B.edgeSet
      rw [hcover]
    have hb : ¬ B.Adj v w := fun h => hv ⟨w, h⟩
    tauto
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  rw [hn]

lemma even_left_of_one_vertex_separation {V : Type*} [Fintype V]
    {G A B : SimpleGraph V} (heven : ∀ v, Even (G.degree v))
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1) :
    ∀ v, Even (A.degree v) := by
  have hout : ∀ v, v ∉ A.support ∩ B.support → Even (A.degree v) := by
    intro v hv
    by_cases ha : v ∈ A.support
    · have hb : v ∉ B.support := fun hb => hv ⟨ha, hb⟩
      rw [degree_eq_of_other_unsupported hcover v hb]
      exact heven v
    · rw [(A.degree_eq_zero_iff_notMem_support v).mpr ha]
      decide
  by_cases hn : (A.support ∩ B.support).Nonempty
  · obtain ⟨c, hc⟩ := hn
    have hsub : (A.support ∩ B.support).Subsingleton :=
      Set.ncard_le_one_iff_subsingleton.mp hover
    have hexc : ∀ v, v ≠ c → Even (A.degree v) := by
      intro v hvc
      apply hout
      intro hv
      exact hvc (hsub hv hc)
    have hsum : Even (∑ v ∈ (Finset.univ : Finset V).erase c, A.degree v) := by
      apply Finset.even_sum
      intro v hv
      exact hexc v (Finset.mem_erase.mp hv).1
    have htotal : Even (∑ v, A.degree v) := by
      rw [A.sum_degrees_eq_twice_card_edges]
      exact even_two_mul _
    have heq := Finset.add_sum_erase (Finset.univ : Finset V) (fun v => A.degree v)
      (Finset.mem_univ c)
    have hcEven : Even (A.degree c) := by
      rw [← heq] at htotal
      exact (Nat.even_add.mp htotal).mpr hsum
    intro v
    by_cases hv : v = c
    · subst v
      exact hcEven
    · exact hexc v hv
  · intro v
    exact hout v (fun hv => hn ⟨v, hv⟩)

lemma hasEvenOneVertexSplit_iff {V : Type*} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) :
    HasEvenOneVertexSplit G ↔
      ∃ A B : SimpleGraph V,
        A ≤ G ∧ B ≤ G ∧ A ≠ ⊥ ∧ B ≠ ⊥ ∧
        Disjoint A.edgeSet B.edgeSet ∧ A.edgeSet ∪ B.edgeSet = G.edgeSet ∧
        (A.support ∩ B.support).ncard ≤ 1 := by
  constructor
  · rintro ⟨A, B, hA, hB, hAne, hBne, _, _, hab, hcover, hover⟩
    exact ⟨A, B, hA, hB, hAne, hBne, hab, hcover, hover⟩
  · rintro ⟨A, B, hA, hB, hAne, hBne, hab, hcover, hover⟩
    refine ⟨A, B, hA, hB, hAne, hBne, ?_, ?_, hab, hcover, hover⟩
    · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using even_left_of_one_vertex_separation heven hcover hover
    · have hcover' : B.edgeSet ∪ A.edgeSet = G.edgeSet := by
        simpa [Set.union_comm] using hcover
      have hover' : (B.support ∩ A.support).ncard ≤ 1 := by
        simpa [Set.inter_comm] using hover
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using even_left_of_one_vertex_separation heven hcover' hover'

end Erdos184
