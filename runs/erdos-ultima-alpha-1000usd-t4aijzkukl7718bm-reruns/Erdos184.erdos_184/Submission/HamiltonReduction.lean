import Submission.ExpandCover
import Submission.ComponentsBound

/-! Auxiliary reductions for Erdős 184. No linear cycle bound is claimed here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

/-- A connected finite even graph contains a sparse connected spanning even subgraph. -/
lemma sparse_spanning_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (he : ∀ v, Even (G.degree v)) :
    ∃ R : SimpleGraph V, R ≤ G ∧ R.Connected ∧
      (∀ v, Even (R.degree v)) ∧ R.edgeFinset.card + 1 ≤ 2 * Fintype.card V := by
  obtain ⟨T, hTG, ht⟩ := hc.exists_isTree_le
  obtain ⟨s, hs, hb⟩ := parity_correction (G \ T)
  let B := (G \ T).deleteEdges (s : Set (Sym2 V))
  let R := G \ B
  have hBG : B ≤ G := ((G \ T).deleteEdges_le _).trans sdiff_le
  have hTR : T ≤ R := by
    intro u v huv
    exact ⟨hTG huv, fun hbuv => hbuv.1.2 huv⟩
  refine ⟨R, sdiff_le, ht.isConnected.mono hTR, ?_, ?_⟩
  · intro v
    have hdeg : R.degree v = G.degree v - B.degree v := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using degree_sdiff_of_le hBG v
    obtain ⟨a, ha⟩ := he v
    have hb' : Even (B.degree v) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hb v
    obtain ⟨b, hb'⟩ := hb'
    have hh : Even (G.degree v - B.degree v) := ⟨a - b, by omega⟩
    rw [← hdeg] at hh
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hh
  · have hsub : R.edgeFinset ⊆ T.edgeFinset ∪ s := by
      intro e he
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset] at *
      change e ∈ (G \ B).edgeSet at he
      rw [SimpleGraph.edgeSet_sdiff] at he
      have hn := he.2
      change e ∉ ((G \ T).deleteEdges (s : Set (Sym2 V))).edgeSet at hn
      rw [SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_sdiff] at hn
      by_cases heT : e ∈ T.edgeSet
      · exact Or.inl heT
      · exact Or.inr (by simpa only [Set.mem_diff, Finset.mem_coe, he.1, heT,
          not_false_eq_true, and_self, true_and, not_not] using hn)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have htcard := ht.card_edgeFinset
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard htcard hs ⊢
    omega

/-- Every connected nontrivial even graph is an edge-bijective image of an even graph
containing a specified spanning cycle, with fewer than twice as many vertices. -/
lemma exists_cycleGraph_expansion {V : Type*} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hc : G.Connected) (he : ∀ v, Even (G.degree v)) :
    ∃ n, ∃ K : SimpleGraph (Fin (n + 3)),
      cycleGraph (n + 3) ≤ K ∧ (∀ w, Even (K.degree w)) ∧
      n + 3 + 1 ≤ 2 * Fintype.card V ∧
      ∃ π : K →g G,
        Set.InjOn (Sym2.map π) K.edgeSet ∧
        Set.SurjOn (Sym2.map π) K.edgeSet G.edgeSet ∧
        ∃ B : Set (Fin (n + 3)), Set.InjOn π Bᶜ ∧ (∀ w ∈ B, K.degree w = 2) ∧
          B.ncard + Fintype.card V = n + 3 := by
  obtain ⟨R, hRG, hcR, heR, hsize⟩ := sparse_spanning_even G hc he
  have hRne : R ≠ ⊥ := by
    intro h
    exact SimpleGraph.not_connected_bot (h ▸ hcR)
  obtain ⟨u, p, hp⟩ := exists_eulerian_closed_walk R hcR heR
  have hlen : p.length = R.edgeFinset.card := by
    have hh := congrArg Finset.card hp.edgesFinset_eq
    simpa only [Walk.IsTrail.edgesFinset, Finset.card_mk, Multiset.coe_card,
      Walk.length_edges] using hh
  obtain ⟨v, q, hq⟩ := exists_cycle_of_even_nonempty R heR hRne
  have hthree : 3 ≤ p.length := by
    rw [hlen]
    exact hq.three_le_length.trans hq.isTrail.length_le_card_edgeFinset
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 3 := ⟨p.length - 3, by omega⟩
  let f := tourCycleHom p hn
  have hb := tourCycleHom_edge_bijective p hn hp
  have hv := edge_surjective_vertex_surjective f hb.2 hcR.preconnected.exists_adj_of_nontrivial
  have hr : (cycleGraph (n + 3)).IsRegularOfDegree 2 := by
    intro w
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (cycleGraph_degree_three_le (v := w))
  obtain ⟨K, hCK, heK, π, hiπ, hsπ, B, hiB, hdB, hBcard⟩ :=
    extend_regular_two_cover G R hRG he heR (cycleGraph (n + 3)) (by
      intro w
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using hr w) f hb.1 hb.2 hv
  refine ⟨n, K, hCK, ?_, ?_, π, hiπ, hsπ, B, hiB, ?_, ?_⟩
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heK
  · simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlen hsize ⊢
    omega
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hdB
  · simpa only [Fintype.card_fin] using hBcard

/-- A linear bound just for graphs containing the standard spanning cycle gives a
linear bound for every connected even graph. The hypothesis here is not proved. -/
lemma connected_even_bound_of_cycleGraph_bound (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n (K : SimpleGraph (Fin (n + 3))),
      cycleGraph (n + 3) ≤ K → (∀ w, Even (K.degree w)) →
      ∃ D : Finset K.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition K D ∧ (D.card : ℝ) ≤ C * (n + 3)) :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ (2 * C + 1) * Fintype.card V := by
  intro V _ G hc he
  cases subsingleton_or_nontrivial V with
  | inl hsub =>
    haveI := hsub
    have hbot : G = ⊥ := Subsingleton.elim _ _
    subst G
    refine ⟨∅, by simp, by simp [IsDecomposition], ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  | inr hnt =>
    haveI := hnt
    obtain ⟨n, K, hCK, heK, hsize, π, hiπ, hsπ, B, hiB, hdB, hBcard⟩ :=
      exists_cycleGraph_expansion G hc he
    obtain ⟨D, hcy, hd, hcard⟩ := hbound n K hCK (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heK)
    obtain ⟨E, hcE, hdE, hcardE⟩ := project_decomposition_degree_two π hiπ hsπ B hiB
      (by simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hdB)
      D (by
        intro H hH
        refine ⟨(hcy H hH).1, ?_⟩
        intro v
        simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using (hcy H hH).2 v) hd
    refine ⟨E, ?_, hdE, ?_⟩
    · intro H hH
      refine ⟨(hcE H hH).1, ?_⟩
      intro v
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcE H hH).2 v
    · have hs' : (n : ℝ) + 3 ≤ 2 * Fintype.card V := by exact_mod_cast (show n + 3 ≤ 2 * Fintype.card V by omega)
      have hb' : (B.ncard : ℝ) ≤ Fintype.card V := by exact_mod_cast (show B.ncard ≤ Fintype.card V by omega)
      have he' : (E.card : ℝ) ≤ (D.card : ℝ) + B.ncard := by exact_mod_cast hcardE
      have hh := mul_le_mul_of_nonneg_left hs' hC
      nlinarith

universe u
/-- This is a reduction, not a proof of the still-unproved hypothesis `hbound`. -/
lemma cycleGraph_bound_suffices (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n (K : SimpleGraph (Fin (n + 3))),
      cycleGraph (n + 3) ≤ K → (∀ w, Even (K.degree w)) →
      ∃ D : Finset K.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition K D ∧ (D.card : ℝ) ≤ C * (n + 3)) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨2 * C + 1, ?_⟩
  intro V _ _ G he
  exact even_bound_of_connected_bound (2 * C + 1)
    (connected_even_bound_of_cycleGraph_bound C hC hbound) G he

lemma decomposition_edge_transversal_bound {V : Type*} [Fintype V]
    (G R : SimpleGraph V) (D : Finset G.Subgraph) (hd : IsDecomposition G D)
    (hhit : ∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) :
    D.card ≤ R.edgeFinset.card := by
  have hex : ∀ H : {H // H ∈ D}, ∃ e : Sym2 V, e ∈ H.val.edgeSet ∧ e ∈ R.edgeSet :=
    fun H => hhit H.val H.property
  choose f hf using hex
  let g : {H // H ∈ D} → R.edgeSet := fun H => ⟨f H, (hf H).2⟩
  have hg : Function.Injective g := by
    intro H K h
    have hef : f H = f K := congrArg Subtype.val h
    apply Subtype.ext
    by_contra hHK
    exact Set.disjoint_left.mp (hd.1 H.property K.property hHK) (hf H).1
      (hef.symm ▸ (hf K).1)
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe, SimpleGraph.edgeFinset_card] using hc

lemma regular_two_graph_edge_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hr : G.IsRegularOfDegree 2) :
    G.edgeFinset.card = Fintype.card V := by
  have hs := G.sum_degrees_eq_twice_card_edges
  have hdeg (v : V) : Nat.card (G.neighborSet v) = 2 := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hs ⊢
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hs
  omega

/-- The Hamilton-cycle hitting assertion is sufficient, but is not established here. -/
lemma cycleGraph_hitting_suffices
    (hhit : ∀ n (K : SimpleGraph (Fin (n + 3))),
      cycleGraph (n + 3) ≤ K → (∀ w, Even (K.degree w)) →
      ∃ D : Finset K.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition K D ∧
        (∀ H ∈ D, (H.edgeSet ∩ (cycleGraph (n + 3)).edgeSet).Nonempty)) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply cycleGraph_bound_suffices 1 (by norm_num)
  intro n K hCK he
  obtain ⟨D, hc, hd, hm⟩ := hhit n K hCK he
  refine ⟨D, hc, hd, ?_⟩
  have hb := decomposition_edge_transversal_bound K (cycleGraph (n + 3)) D hd hm
  have heq := regular_two_graph_edge_card (cycleGraph (n + 3)) (by
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using cycleGraph_degree_three_le (v := v))
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb heq
  rw [heq] at hb
  simp only [Nat.card_fin] at hb
  norm_num only [one_mul]
  exact_mod_cast hb

end Erdos184
