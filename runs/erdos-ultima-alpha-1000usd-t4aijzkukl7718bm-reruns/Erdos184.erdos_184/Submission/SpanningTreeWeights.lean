import Submission.RankReduction

/-!
Uniform spanning-tree edge weights and their cycle-partition counting identity.
No assertion that a uniformly heavy cycle decomposition exists is made here.
The definition is combinatorial; identifying it with electrical effective
resistance would require an additional theorem and is not used below.
-/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184.SpanningTreeWeights

variable {V : Type*} [Fintype V]

noncomputable def trees (G : SimpleGraph V) : Finset (SimpleGraph V) :=
  {T | T ≤ G ∧ T.IsTree}.toFinset

@[simp] lemma mem_trees (G T : SimpleGraph V) : T ∈ trees G ↔ T ≤ G ∧ T.IsTree := by
  simp [trees]

lemma trees_nonempty {G : SimpleGraph V} (hG : G.Connected) : (trees G).Nonempty := by
  obtain ⟨T,hTG,hT⟩ := hG.exists_isTree_le
  exact ⟨T,(mem_trees G T).mpr ⟨hTG,hT⟩⟩

noncomputable def weight (G : SimpleGraph V) (e : Sym2 V) : ℝ :=
  ((trees G).filter (fun T => e ∈ T.edgeSet)).card / ((trees G).card : ℝ)

noncomputable def mass (G : SimpleGraph V) (S : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ S, weight G e

lemma weight_nonneg (G : SimpleGraph V) (e : Sym2 V) : 0 ≤ weight G e := by
  unfold weight
  positivity

lemma mass_nonneg (G : SimpleGraph V) (S : Finset (Sym2 V)) : 0 ≤ mass G S := by
  exact Finset.sum_nonneg (fun e _ => weight_nonneg G e)

lemma weight_eq_average (G : SimpleGraph V) (e : Sym2 V) :
    weight G e = (∑ T ∈ trees G, if e ∈ T.edgeSet then (1 : ℝ) else 0) /
      (trees G).card := by
  simp [weight, Finset.sum_boole]

lemma mass_eq_average (G : SimpleGraph V) (S : Finset (Sym2 V)) :
    mass G S = (∑ T ∈ trees G, ((S ∩ T.edgeFinset).card : ℝ)) /
      (trees G).card := by
  simp only [mass, weight_eq_average, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  simp only [← mem_edgeFinset]
  rw [Finset.sum_boole]
  congr 1

lemma mass_edges {G : SimpleGraph V} (hG : G.Connected) :
    mass G G.edgeFinset = (Fintype.card V - 1 : ℕ) := by
  rw [mass_eq_average]
  have hterm : ∀ T ∈ trees G,
      ((G.edgeFinset ∩ T.edgeFinset).card : ℝ) = (Fintype.card V - 1 : ℕ) := by
    intro T hT
    obtain ⟨hTG,hT⟩ := (mem_trees G T).mp hT
    have hsub : T.edgeFinset ⊆ G.edgeFinset := by simpa using hTG
    rw [Finset.inter_eq_right.mpr hsub]
    exact_mod_cast (show T.edgeFinset.card = Fintype.card V - 1 by
      have hh := hT.card_edgeFinset
      omega)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (trees G).card := by
    exact_mod_cast Finset.card_pos.mpr (trees_nonempty hG)
  field_simp

lemma one_le_mass_of_hits {G : SimpleGraph V} (hG : G.Connected)
    (S : Finset (Sym2 V))
    (hh : ∀ T ∈ trees G, (S ∩ T.edgeFinset).Nonempty) : 1 ≤ mass G S := by
  rw [mass_eq_average]
  have hpos : (0 : ℝ) < (trees G).card := by
    exact_mod_cast Finset.card_pos.mpr (trees_nonempty hG)
  apply (le_div_iff₀ hpos).mpr
  simp only [one_mul]
  calc
    ((trees G).card : ℝ) = ∑ T ∈ trees G, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun T hT => by
      exact_mod_cast Finset.card_pos.mpr (hh T hT))

lemma exists_tree_disjoint_of_mass_lt_one {G : SimpleGraph V} (hG : G.Connected)
    (S : Finset (Sym2 V)) (hm : mass G S < 1) :
    ∃ T ∈ trees G, Disjoint S T.edgeFinset := by
  by_contra! hh
  have hh' : ∀ T ∈ trees G, (S ∩ T.edgeFinset).Nonempty := by
    intro T hT
    exact Finset.not_disjoint_iff_nonempty_inter.mp (hh T hT)
  exact (one_le_mass_of_hits hG S hh').not_gt hm

lemma mass_decomposition (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hd : IsDecomposition G D) :
    ∑ H ∈ D, mass G H.edgeSet.toFinset = mass G G.edgeFinset := by
  have hdis : Set.PairwiseDisjoint (D : Set G.Subgraph)
      (fun H => H.edgeSet.toFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hd.1 hH hK hne)
      (Set.mem_toFinset.mp heH) (Set.mem_toFinset.mp heK)
  have hunion : D.biUnion (fun H => H.edgeSet.toFinset) = G.edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion, Set.mem_toFinset, mem_edgeFinset]
    simpa using Set.ext_iff.mp hd.2 e
  unfold mass
  rw [← hunion, Finset.sum_biUnion hdis]

lemma decomposition_bound {G : SimpleGraph V} (hG : G.Connected)
    (D : Finset G.Subgraph) (hd : IsDecomposition G D) (ε : ℝ)
    (hw : ∀ H ∈ D, ε ≤ mass G H.edgeSet.toFinset) :
    ε * D.card ≤ (Fintype.card V - 1 : ℕ) := by
  calc
    ε * D.card = ∑ H ∈ D, ε := by simp [mul_comm]
    _ ≤ ∑ H ∈ D, mass G H.edgeSet.toFinset := Finset.sum_le_sum hw
    _ = mass G G.edgeFinset := mass_decomposition G D hd
    _ = _ := mass_edges hG

lemma connected_deleteEdges_of_mass_lt_one {G : SimpleGraph V} (hG : G.Connected)
    (S : Finset (Sym2 V)) (hm : mass G S < 1) :
    (G.deleteEdges (S : Set (Sym2 V))).Connected := by
  obtain ⟨T,hT,hdis⟩ := exists_tree_disjoint_of_mass_lt_one hG S hm
  obtain ⟨hTG,hT⟩ := (mem_trees G T).mp hT
  apply hT.isConnected.mono
  intro u v huv
  apply deleteEdges_adj.mpr
  refine ⟨hTG huv,?_⟩
  intro he
  exact Finset.disjoint_left.mp hdis he (mem_edgeFinset.mpr (show s(u,v) ∈ T.edgeSet from huv))

lemma one_le_mass_of_disconnecting {G : SimpleGraph V} (hG : G.Connected)
    (S : Finset (Sym2 V)) (hdisc : ¬(G.deleteEdges (S : Set (Sym2 V))).Connected) :
    1 ≤ mass G S := by
  by_contra! h
  exact hdisc (connected_deleteEdges_of_mass_lt_one hG S h)

lemma one_le_mass_of_disconnecting_subgraph {G : SimpleGraph V} (hG : G.Connected)
    (H : G.Subgraph) (hdisc : ¬(G \ H.spanningCoe).Connected) :
    1 ≤ mass G H.edgeSet.toFinset := by
  apply one_le_mass_of_disconnecting hG
  have heq : G.deleteEdges (H.edgeSet.toFinset : Set (Sym2 V)) = G \ H.spanningCoe := by
    ext u v
    simp
  rwa [heq]

lemma one_le_mass_of_degree_two {G : SimpleGraph V} (hG : G.Connected)
    (H : G.Subgraph) (hreg : H.coe.IsRegularOfDegree 2) (v : V)
    (hv : v ∈ H.verts) (hdeg : G.degree v = 2) :
    1 ≤ mass G H.edgeSet.toFinset := by
  haveI : Nontrivial V := G.nontrivial_of_degree_ne_zero (v := v) (by omega)
  apply one_le_mass_of_disconnecting_subgraph hG H
  intro hconn
  have hpos := hconn.preconnected.degree_pos_of_nontrivial v
  have hH : H.spanningCoe.degree v = 2 := by
    rw [Subgraph.degree_spanningCoe, ← H.coe_degree ⟨v,hv⟩]
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hreg ⟨v,hv⟩
  have hdiff := degree_sdiff_of_le H.spanningCoe_le v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hpos hH hdiff hdeg
  omega

universe u

/-- This is a conditional reduction. Its heavy-decomposition hypothesis is
not proved by any of the preceding counting or connectivity lemmas. -/
theorem conjecture_of_heavy_decompositions (ε : ℝ) (hε : 0 < ε)
    (heavy : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (∀ H ∈ D, ε ≤ mass G H.edgeSet.toFinset)) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply RankReduction.conjecture_iff_rank_bound.mpr
  obtain ⟨C,hC⟩ := exists_nat_ge ε⁻¹
  refine ⟨C,?_⟩
  intro V _ G he
  apply RankComponents.bound_of_component_bounds
  intro k
  have hek : ∀ x, Even (k.toSimpleGraph.degree x) := by
    intro x
    have hx := he x.val
    have hd := component_degree G k x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hd ⊢
    rwa [hd]
  obtain ⟨D,hcy,hd,hw⟩ := heavy k.toSimpleGraph k.connected_toSimpleGraph hek
  have hb := decomposition_bound k.connected_toSimpleGraph D hd ε hw
  have hr := RankCriticalPartitions.connected_rank k.connected_toSimpleGraph
  have heq : RankCritical.graphRank k.toSimpleGraph = Fintype.card k - 1 := by omega
  refine ⟨D,hcy,hd,?_⟩
  rw [heq]
  have hb' : (D.card : ℝ) ≤ (C : ℝ) * (Fintype.card k - 1 : ℕ) := by
    calc
      (D.card : ℝ) ≤ (Fintype.card k - 1 : ℕ) / ε :=
        (le_div_iff₀ hε).mpr (by nlinarith [hb])
      _ = ε⁻¹ * (Fintype.card k - 1 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)
  exact_mod_cast hb'

end Erdos184.SpanningTreeWeights
