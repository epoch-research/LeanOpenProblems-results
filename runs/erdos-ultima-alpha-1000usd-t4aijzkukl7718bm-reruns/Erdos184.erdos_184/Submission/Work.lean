import FormalConjecturesUtil

/-!
# Erdős Problem 184

*References:*
- [erdosproblems.com/184](https://www.erdosproblems.com/184)
- [BM22] Bucić, M. and Montgomery, R., Towards the Erdős-Gallai Cycle Decomposition Conjecture.
  arXiv:2211.07689 (2022).
- [CFS14] Conlon, David and Fox, Jacob and Sudakov, Benny, Cycle packing. Random Structures
  Algorithms (2014), 608-626.
- [EGP66] Erdős, Paul and Goodman, A. W. and Pósa, Lajos, The representation of a graph by set
  intersections. Canadian J. Math. (1966), 106-112.
- [Er71] Erdős, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial
  Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open Filter SimpleGraph

namespace Erdos184

/--
A graph $H$ is a cycle or an edge if it is connected and 2-regular, or if it has exactly one edge.
-/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

/-- D is a decomposition of G into subgraphs. -/
def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet


open scoped Classical

lemma coe_edgeFinset_card {V : Type*} (G : SimpleGraph V) [Fintype V] (H : G.Subgraph) :
    H.coe.edgeFinset.card = H.edgeSet.ncard := by
  change H.coe.edgeSet.toFinset.card = _
  rw [← Set.ncard_eq_toFinset_card']
  rw [← H.image_coe_edgeSet_coe]
  exact (Set.ncard_image_of_injective _
    (Sym2.map.injective Subtype.val_injective)).symm

lemma exists_edge_subgraph {V : Type*} [Fintype V] (G : SimpleGraph V)
    (e : G.edgeSet) :
    ∃ H : G.Subgraph, H.edgeSet = {e.val} ∧ IsCycleOrEdge H.coe := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
    refine ⟨G.subgraphOfAdj he, G.edgeSet_subgraphOfAdj he, Or.inr ?_⟩
    rw [coe_edgeFinset_card, G.edgeSet_subgraphOfAdj he]
    simp

noncomputable def oneEdge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (e : G.edgeSet) : G.Subgraph :=
  Classical.choose (exists_edge_subgraph G e)

lemma oneEdge_spec {V : Type*} [Fintype V] (G : SimpleGraph V) (e : G.edgeSet) :
    (oneEdge G e).edgeSet = {e.val} ∧ IsCycleOrEdge (oneEdge G e).coe :=
  Classical.choose_spec (exists_edge_subgraph G e)

lemma edge_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ G.edgeFinset.card := by
  let D := Finset.univ.image (oneEdge G)
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hH
    exact (oneEdge_spec G e).2
  · intro H hH K hK hHK
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hK
    change Disjoint (oneEdge G e).edgeSet (oneEdge G f).edgeSet
    rw [(oneEdge_spec G e).1, (oneEdge_spec G f).1]
    exact Set.disjoint_singleton.mpr (fun hef => hHK (congrArg _ (Subtype.ext hef)))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, hH, he⟩
      exact H.edgeSet_subset he
    · intro he
      refine ⟨oneEdge G ⟨e, he⟩, Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [(oneEdge_spec G ⟨e, he⟩).1]
      exact Set.mem_singleton e
  · calc
      D.card ≤ (Finset.univ : Finset G.edgeSet).card := Finset.card_image_le
      _ = G.edgeFinset.card := G.edgeSet_univ_card

lemma quadratic_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      D.card ≤ (Fintype.card V).choose 2 := by
  obtain ⟨D, hD, hd, hc⟩ := edge_decomposition G
  exact ⟨D, hD, hd, hc.trans G.card_edgeFinset_le_card_choose_two⟩


universe u

lemma asymptotic_iff_linear :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card V) := by
  constructor
  · rintro ⟨f, hf, hdec⟩
    obtain ⟨c, hc, hcf⟩ := hf.exists_pos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcf.bound
    refine ⟨c + N, ?_⟩
    intro V _ _ G
    by_cases hn : N ≤ Fintype.card V
    · obtain ⟨D, hD, hd, hcard⟩ := hdec G
      refine ⟨D, hD, hd, hcard.trans ?_⟩
      have hh : |f (Fintype.card V)| ≤ c * Fintype.card V := by
        simpa only [Real.norm_eq_abs, Nat.abs_cast] using hN (Fintype.card V) hn
      calc
        f (Fintype.card V) ≤ |f (Fintype.card V)| := le_abs_self _
        _ ≤ c * Fintype.card V := hh
        _ ≤ (c + N) * Fintype.card V := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · obtain ⟨D, hD, hd, hcard⟩ := quadratic_decomposition G
      refine ⟨D, hD, hd, ?_⟩
      have hsmall : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_not_ge hn)
      have hquad : (D.card : ℝ) ≤ (Fintype.card V : ℝ)^2 := by
        exact_mod_cast hcard.trans (Nat.choose_le_pow _ _)
      calc
        (D.card : ℝ) ≤ (Fintype.card V : ℝ)^2 := hquad
        _ ≤ N * Fintype.card V := by nlinarith
        _ ≤ (c + N) * Fintype.card V := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact le_add_of_nonneg_left hc.le
  · rintro ⟨C, hC⟩
    exact ⟨fun n ↦ C * n, Asymptotics.isBigO_const_mul_self C _ _, hC⟩


lemma sparse_sum_mod_two {E V : Type*} [Fintype E] [Fintype V]
    (v : E → V → ZMod 2) :
    ∃ s : Finset E, s.card ≤ Fintype.card V ∧ ∑ e ∈ s, v e = ∑ e, v e := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (ZMod 2) v
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hsum : (∑ e, v e) ∈ Submodule.span (ZMod 2) (Set.range (v ∘ a)) := by
    rw [hspan]
    exact Submodule.sum_mem _ (fun e _ => Submodule.subset_span ⟨e, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hsum
  let t : Finset κ := Finset.univ.filter (fun i => c i = 1)
  refine ⟨t.image a, ?_, ?_⟩
  · calc
      (t.image a).card ≤ t.card := Finset.card_image_le
      _ ≤ Fintype.card κ := Finset.card_le_univ _
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := hli.fintype_card_le_finrank
      _ = Fintype.card V := by simp
  · rw [Finset.sum_image (fun i _ j _ h => ha h)]
    rw [← hc]
    dsimp [t]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    have hz : c i = 0 ∨ c i = 1 := by
      have hval := (c i).val_lt
      have hcases : (c i).val = 0 ∨ (c i).val = 1 := by omega
      rcases hcases with h | h
      · left; apply ZMod.val_injective; simpa using h
      · right; apply ZMod.val_injective; simpa using h
    rcases hz with h | h <;> simp [h]


lemma parity_correction {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ s : Finset (Sym2 V), s.card ≤ Fintype.card V ∧
      ∀ x, Even ((G.deleteEdges (s : Set (Sym2 V))).degree x) := by
  obtain ⟨s, hs, hsum⟩ := sparse_sum_mod_two (fun e x => G.incMatrix (ZMod 2) x e)
  refine ⟨s, hs, ?_⟩
  intro x
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hinc (e : Sym2 V) :
      (G.deleteEdges (s : Set (Sym2 V))).incMatrix (ZMod 2) x e =
        if e ∈ s then 0 else G.incMatrix (ZMod 2) x e := by
    simp only [SimpleGraph.incMatrix_apply', SimpleGraph.incidenceSet,
      SimpleGraph.edgeSet_deleteEdges, Set.mem_setOf_eq, Set.mem_diff, Finset.mem_coe]
    by_cases he : e ∈ s <;> simp [he]
  have hx := congrFun hsum x
  simp only [Finset.sum_apply] at hx
  have hh :
      (∑ e, (G.deleteEdges (s : Set (Sym2 V))).incMatrix (ZMod 2) x e) +
        (∑ e ∈ s, G.incMatrix (ZMod 2) x e) = ∑ e, G.incMatrix (ZMod 2) x e := by
    calc
      _ = ∑ e, ((G.deleteEdges (s : Set (Sym2 V))).incMatrix (ZMod 2) x e +
          if e ∈ s then G.incMatrix (ZMod 2) x e else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : e ∈ s <;> simp [hinc, he]
  rw [hx] at hh
  have hz : (∑ e, (G.deleteEdges (s : Set (Sym2 V))).incMatrix (ZMod 2) x e) = 0 := by
    simpa using hh
  simpa only [SimpleGraph.sum_incMatrix_apply] using hz


def promote {V : Type*} {G A : SimpleGraph V} (hA : A ≤ G) (H : A.Subgraph) : G.Subgraph where
  verts := H.verts
  Adj := H.Adj
  adj_sub h := hA (H.adj_sub h)
  edge_vert := H.edge_vert
  symm := H.symm

lemma promote_edgeSet {V : Type*} {G A : SimpleGraph V} (hA : A ≤ G) (H : A.Subgraph) :
    (promote hA H).edgeSet = H.edgeSet := rfl

lemma combine_decompositions {V : Type*} [Fintype V] {G A B : SimpleGraph V}
    (hA : A ≤ G) (hB : B ≤ G)
    (hab : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (DA : Finset A.Subgraph) (DB : Finset B.Subgraph)
    (hca : ∀ H ∈ DA, IsCycleOrEdge H.coe) (hcb : ∀ H ∈ DB, IsCycleOrEdge H.coe)
    (hda : IsDecomposition A DA) (hdb : IsDecomposition B DB) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card ≤ DA.card + DB.card := by
  let D := DA.image (promote hA) ∪ DB.image (promote hB)
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      exact hca K hK
    · obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hH
      exact hcb K hK
  · intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hda.1 hX hY (fun h => hne (congrArg (promote hA) h))
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hab.mono X.edgeSet_subset Y.edgeSet_subset
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hab.symm.mono X.edgeSet_subset Y.edgeSet_subset
    · obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hK
      exact hdb.1 hX hY (fun h => hne (congrArg (promote hB) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H, _, he⟩
      exact H.edgeSet_subset he
    · intro he
      rw [← hcover] at he
      rcases he with he | he
      · rw [← hda.2] at he
        simp only [Set.mem_iUnion] at he
        obtain ⟨H, hH, he⟩ := he
        exact ⟨promote hA H, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), he⟩
      · rw [← hdb.2] at he
        simp only [Set.mem_iUnion] at he
        obtain ⟨H, hH, he⟩ := he
        exact ⟨promote hB H, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨H, hH, rfl⟩), he⟩
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)


lemma linear_bound_of_even_bound (C : ℝ)
    (hC : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ x, Even (G.degree x)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card V) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ (C + 1) * Fintype.card V := by
  intro V _ _ G
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
  obtain ⟨DA, hca, hda, hcarda⟩ := hC A (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heven)
  obtain ⟨DB, hcb, hdb, hcardb⟩ := edge_decomposition B
  obtain ⟨D, hc, hd, hcard⟩ := combine_decompositions hA hB hab hcover DA DB hca hcb hda hdb
  refine ⟨D, hc, hd, ?_⟩
  have hdb' : (DB.card : ℝ) ≤ Fintype.card V := by
    have hh := hbcard.trans hs
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh hcardb
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using hcardb.trans hh : DB.card ≤ Fintype.card V)
  have hd' : (D.card : ℝ) ≤ (DA.card : ℝ) + DB.card := by exact_mod_cast hcard
  nlinarith


lemma bounded_degree_decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d : ℕ) (hdeg : ∀ x, G.degree x ≤ d) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
      2 * D.card ≤ d * Fintype.card V := by
  obtain ⟨D, hc, hd, hcard⟩ := edge_decomposition G
  refine ⟨D, hc, hd, ?_⟩
  have hsum : ∑ x, G.degree x ≤ ∑ _x : V, d :=
    Finset.sum_le_sum (fun x _ => hdeg x)
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  simpa [mul_comm] using (Nat.mul_le_mul_left 2 hcard).trans hsum

lemma conjecture_iff_even_bound :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℝ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ x, Even (G.degree x)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card V) := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := asymptotic_iff_linear.mp h
    exact ⟨C, fun G _ => hC G⟩
  · rintro ⟨C, hC⟩
    exact asymptotic_iff_linear.mpr ⟨C + 1, linear_bound_of_even_bound C hC⟩

end Erdos184
