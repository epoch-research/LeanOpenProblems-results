import Submission.BudgetedPackingCritical

/-!
Global maximum-coverage consequences and an exact near-cover reformulation.
The existence of uniform near-cover constants is NOT established here.
-/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184.BudgetedCyclePacking
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Feasible.weight_eq_covered {k : ℕ} {D : Finset G.Subgraph}
    (hD : Feasible G k D) : weight D = (unionPieces G D).edgeSet.ncard := by
  have h := unionPieces_edge_card G D hD.2.1
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, weight] using h.symm

/-- Coverage optimality is exactly residual-edge minimization. -/
lemma Optimal.residual_card_le {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (E : Finset G.Subgraph) (hE : Feasible G k E) :
    (G \ unionPieces G D).edgeSet.ncard ≤ (G \ unionPieces G E).edgeSet.ncard := by
  have hDpart := cycle_packing_edge_card_partition G D hm.1.2.1
  have hEpart := cycle_packing_edge_card_partition G E hE.2.1
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hDpart hEpart
  have hmax := hm.2 E hE
  unfold weight at hmax
  omega

omit [Fintype V] in
lemma residual_eq_bot_of_decomposition (E : Finset G.Subgraph)
    (hd : IsDecomposition G E) : G \ unionPieces G E = ⊥ := by
  have hU : unionPieces G E = G := by
    apply SimpleGraph.edgeSet_injective
    rw [unionPieces_edgeSet, hd.2]
  rw [hU, sdiff_self]

lemma Optimal.residual_eq_bot_of_decomposition {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G E) (hb : E.card ≤ k) :
    G \ unionPieces G D = ⊥ := by
  have h := hm.residual_card_le E ⟨hc,hd.1,hb⟩
  rw [Erdos184.BudgetedCyclePacking.residual_eq_bot_of_decomposition E hd] at h
  have hz : (G \ unionPieces G D).edgeFinset.card = 0 := by
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] at *
    simpa using h
  exact SimpleGraph.edgeFinset_eq_empty.mp (Finset.card_eq_zero.mp hz)

/-- If an even residual is nonempty, a maximum-coverage packing has no
smaller pure-cycle packing with the same covered edges. Such a replacement
would leave a free slot for a residual cycle. -/
lemma Optimal.minimum_for_covered {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (he : ∀ v, Even (G.degree v))
    (hne : G \ unionPieces G D ≠ ⊥)
    (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet))
    (hu : unionPieces G E = unionPieces G D) : D.card ≤ E.card := by
  by_contra h
  have hlt : E.card < k := lt_of_lt_of_le (by omega) hm.1.2.2
  have hE : Feasible G k E := ⟨hc,hd,hlt.le⟩
  have hw : weight E = weight D := by
    rw [hE.weight_eq_covered, hm.1.weight_eq_covered, hu]
  have hopt : Optimal G k E := ⟨hE,fun F hF => (hm.2 F hF).trans_eq hw.symm⟩
  have hh := hopt.residual_eq_bot_of_lt he hlt
  rw [hu] at hh
  exact hne hh

/-- A proper enlargement of the covered edge set cannot be partitioned
using as few cycles as the selected packing. No parity hypothesis on G
is needed for this consequence of genuine global optimality. -/
lemma Optimal.card_lt_of_proper_extension {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet))
    (hproper : (unionPieces G D).edgeSet ⊂ (unionPieces G E).edgeSet) :
    D.card < E.card := by
  by_contra h
  have hE : Feasible G k E := ⟨hc,hd,(show E.card ≤ D.card by omega).trans hm.1.2.2⟩
  have hmax := hm.2 E hE
  rw [hE.weight_eq_covered, hm.1.weight_eq_covered] at hmax
  have hlt := Set.ncard_lt_ncard (ht := Set.toFinite _) hproper
  omega

/-- In particular, adjoining a residual cycle raises the exact packing
minimum by one: the adjoined packing itself has D.card+1 members, and any
pure-cycle packing with the same edge union has at least that many. -/
lemma Optimal.minimum_after_adjoining {k : ℕ} {D : Finset G.Subgraph}
    (hm : Optimal G k D) (K : G.Subgraph)
    (hcK : K.coe.Connected ∧ K.coe.IsRegularOfDegree 2)
    (hdis : ∀ H ∈ D, Disjoint K.edgeSet H.edgeSet)
    (E : Finset G.Subgraph)
    (hc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (E : Set G.Subgraph) (fun H => H.edgeSet))
    (hu : unionPieces G E = unionPieces G (insert K D)) :
    D.card + 1 ≤ E.card := by
  apply hm.card_lt_of_proper_extension E hc hd
  rw [hu, unionPieces_edgeSet, unionPieces_edgeSet]
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · exact Set.iUnion₂_mono' (fun H hH => ⟨H,Finset.mem_insert_of_mem hH,Set.Subset.rfl⟩)
  · intro heq
    obtain ⟨e,he⟩ := cycle_edgeSet_nonempty K hcK.1 hcK.2
    have he' : e ∈ ⋃ H ∈ insert K D, H.edgeSet :=
      Set.mem_iUnion₂.mpr ⟨K,Finset.mem_insert_self _ _,he⟩
    rw [← heq] at he'
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he'
    exact Set.disjoint_left.mp (hdis H hH) he heH

universe u

/-- Exact equivalence with the original proposition. The right-hand side
is a genuinely uniform hypothesis: C and B may not depend on the graph. -/
theorem conjecture_iff_uniform_near_cover :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C B : ℕ, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph, Feasible G (C * Fintype.card V) D ∧
        (G \ unionPieces G D).edgeSet.ncard ≤ B * Fintype.card V) := by
  rw [conjecture_iff_even_cycle_bound]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨C,hC⟩ := exists_nat_ge c
    refine ⟨C,0,?_⟩
    intro V _ G he
    obtain ⟨D,hcy,hd,hb⟩ := hc G he
    have hbd : D.card ≤ C * Fintype.card V := by
      have hh := hb.trans (mul_le_mul_of_nonneg_right hC
        (show (0:ℝ) ≤ Fintype.card V by positivity))
      exact_mod_cast hh
    refine ⟨D,⟨hcy,hd.1,hbd⟩,?_⟩
    rw [residual_eq_bot_of_decomposition D hd]
    simp
  · rintro ⟨C,B,h⟩
    refine ⟨(C:ℝ) + (B:ℝ)/3,?_⟩
    intro V _ _ G he
    obtain ⟨D,hD,hR⟩ := h G he
    obtain ⟨E,hc,hd,hb⟩ := complete_near_cover G he (C * Fintype.card V) D hD
    refine ⟨E,hc,hd,?_⟩
    have hnat : 3 * E.card ≤ 3 * (C * Fintype.card V) + B * Fintype.card V :=
      hb.trans (Nat.add_le_add_left hR _)
    have hreal : (3:ℝ) * E.card ≤ 3 * ((C:ℝ) * Fintype.card V) +
        (B:ℝ) * Fintype.card V := by exact_mod_cast hnat
    nlinarith

/-- One may equivalently require the same residual bound for EVERY global
optimum, not merely for one chosen feasible packing. -/
theorem conjecture_iff_optimal_near_cover :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C B : ℕ, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∀ D : Finset G.Subgraph, Optimal G (C * Fintype.card V) D →
        (G \ unionPieces G D).edgeSet.ncard ≤ B * Fintype.card V) := by
  rw [conjecture_iff_uniform_near_cover]
  constructor
  · rintro ⟨C,B,h⟩
    refine ⟨C,B,?_⟩
    intro V _ G he D hm
    obtain ⟨E,hE,hb⟩ := h G he
    exact (hm.residual_card_le E hE).trans hb
  · rintro ⟨C,B,h⟩
    refine ⟨C,B,?_⟩
    intro V _ G he
    obtain ⟨D,hm⟩ := exists_optimal G (C * Fintype.card V)
    exact ⟨D,hm.1,h G he D hm⟩

end Erdos184.BudgetedCyclePacking
