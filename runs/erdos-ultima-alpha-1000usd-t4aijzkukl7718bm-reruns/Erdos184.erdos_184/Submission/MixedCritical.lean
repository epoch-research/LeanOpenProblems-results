import Submission.ForestMixedCompletion
import Submission.BlockRankPotential

/-!
Criticality for minimum cycle-and-single-edge partitions, under arbitrary
edge restrictions. This module does not assert a bound for critical graphs.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.MixedCritical
open CycleNumberSubmodularity RankCritical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma partition_exists (G : SimpleGraph V) :
    ∃ n : ℕ, ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = n := by
  obtain ⟨D,hc,hd,_⟩ := edge_decomposition G
  exact ⟨D.card,D,hc,hd,rfl⟩

noncomputable def number (G : SimpleGraph V) : ℕ := Nat.find (partition_exists G)

lemma minimum_exists (G : SimpleGraph V) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧ D.card = number G :=
  Nat.find_spec (partition_exists G)

lemma number_le (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D) :
    number G ≤ D.card := Nat.find_min' (partition_exists G) ⟨D,hc,hd,rfl⟩

lemma number_bot : number (⊥ : SimpleGraph V) = 0 := by
  have h := number_le (⊥ : SimpleGraph V) ∅ (by simp) (by simp [IsDecomposition])
  simpa using h

lemma number_le_edges (G : SimpleGraph V) : number G ≤ G.edgeSet.ncard := by
  obtain ⟨D,hc,hd,hb⟩ := edge_decomposition G
  exact (number_le G D hc hd).trans (by simpa only [edgeFinset_card,
    ← Nat.card_eq_fintype_card] using hb)

lemma number_le_restriction_add_edges {A G : SimpleGraph V} (hAG : A ≤ G) :
    number G ≤ number A + (G \ A).edgeSet.ncard := by
  obtain ⟨D,hc,hd,hb⟩ := minimum_exists A
  obtain ⟨E,hcE,hdE,hbE⟩ := edge_decomposition (G \ A)
  obtain ⟨F,hcF,hdF,hbF⟩ := combine_decompositions hAG sdiff_le
    (by rw [edgeSet_sdiff]; exact Set.disjoint_sdiff_right)
    (by rw [edgeSet_sdiff]; exact Set.union_diff_cancel (edgeSet_mono hAG))
    D E hc hcE hd hdE
  have hn := number_le G F hcF hdF
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hbE
  omega

lemma number_le_cycleNumber (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    number G ≤ cycleNumber G := by
  obtain ⟨D,hc,hd,hb⟩ := CountCritical.minimum_exists G he
  have h := number_le G D (by
    intro H hH
    left
    refine ⟨(hc H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hc H hH).2 v) hd
  omega

lemma number_eq_cycleNumber (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    number G = cycleNumber G := by
  apply Nat.le_antisymm (number_le_cycleNumber G he)
  obtain ⟨D,hc,hd,hb⟩ := minimum_exists G
  obtain ⟨E,hcE,hdE,hbE⟩ := ForestMixedCompletion.extend_mixed_decomposition
    (le_refl G) he (by simpa using (show (⊥ : SimpleGraph V).IsAcyclic from isAcyclic_bot))
    D hc hd
  exact (CountCritical.number_le G E hcE hdE).trans (hbE.trans_eq hb)

/-- A forest can be added to an arbitrary restriction of an even graph
without increasing the minimum mixed count. -/
lemma number_le_of_even_forest_complement {A G : SimpleGraph V} (hAG : A ≤ G)
    (he : ∀ v, Even (G.degree v)) (hf : (G \ A).IsAcyclic) : number G ≤ number A := by
  obtain ⟨D,hc,hd,hb⟩ := minimum_exists A
  obtain ⟨E,hcE,hdE,hbE⟩ := ForestMixedCompletion.extend_mixed_decomposition hAG he hf D hc hd
  apply (number_le G E ?_ hdE).trans (hbE.trans_eq hb)
  intro H hH
  left
  refine ⟨(hcE H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using (hcE H hH).2 v

lemma forest_number (G : SimpleGraph V) (hf : G.IsAcyclic) :
    number G = G.edgeSet.ncard := by
  apply Nat.le_antisymm (number_le_edges G)
  obtain ⟨D,hc,hd,hb⟩ := minimum_exists G
  have hs : ∀ H ∈ D, H.edgeSet.ncard = 1 := by
    intro H hH
    rcases hc H hH with hcy | he
    · obtain ⟨e,he,hn⟩ := cycle_has_edge_outside_forest G hf H hcy.1 (by
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcy.2 v)
      exact (hn (H.edgeSet_subset he)).elim
    · rwa [coe_edgeFinset_card] at he
  have hsum := unionPieces_edge_card G D hd.1
  have hu : unionPieces G D = G := by
    apply edgeSet_injective
    rw [unionPieces_edgeSet,hd.2]
  rw [hu] at hsum
  rw [Finset.sum_congr rfl hs] at hsum
  simp only [Finset.sum_const,smul_eq_mul,mul_one,edgeFinset_card,← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hsum
  omega

/-- Strict criticality uses ALL proper edge subgraphs, not just even ones. -/
def IsCritical (k : ℕ) (G : SimpleGraph V) : Prop :=
  number G = k ∧ ∀ A : SimpleGraph V, A ≤ G → A ≠ G → number A < k

lemma delete_edge_properties (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    let A := G.deleteEdges {s(u,v)}
    A ≤ G ∧ A ≠ G ∧ (G \ A).edgeSet = {s(u,v)} := by
  dsimp only
  refine ⟨G.deleteEdges_le _,?_,?_⟩
  · intro h
    have hm : s(u,v) ∈ (G.deleteEdges {s(u,v)}).edgeSet := h.symm ▸ huv
    simpa only [edgeSet_deleteEdges,Set.mem_diff,Set.mem_singleton_iff,
      not_true_eq_false,and_false] using hm
  · rw [edgeSet_sdiff,edgeSet_deleteEdges]
    ext e
    simp only [Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨he,hn⟩
      by_contra hne
      exact hn ⟨he,hne⟩
    · rintro rfl
      exact ⟨huv,fun h => h.2 rfl⟩

lemma extract (G : SimpleGraph V) (k : ℕ) (hk : 0 < k) (hkg : k ≤ number G) :
    ∃ A : SimpleGraph V, A ≤ G ∧ IsCritical k A := by
  let P (m : ℕ) := ∃ A : SimpleGraph V, A ≤ G ∧ k ≤ number A ∧ A.edgeSet.ncard = m
  have hex : ∃ m, P m := ⟨_,G,le_rfl,hkg,rfl⟩
  obtain ⟨A,hAG,hkA,hm⟩ := Nat.find_spec hex
  have hproper (B : SimpleGraph V) (hBA : B ≤ A) (hne : B ≠ A) : number B < k := by
    by_contra hn
    have hmin := Nat.find_min' hex (show P B.edgeSet.ncard from
      ⟨B,hBA.trans hAG,by omega,rfl⟩)
    have hlt := CountCritical.edges_lt hBA hne
    omega
  have hne : A ≠ ⊥ := by
    intro h; rw [h,number_bot] at hkA; omega
  obtain ⟨u,v,huv⟩ := (SimpleGraph.ne_bot_iff_exists_adj).mp hne
  obtain ⟨hle,hneq,hedge⟩ := delete_edge_properties A huv
  have hlo := hproper _ hle hneq
  have hup := number_le_restriction_add_edges hle
  rw [hedge,Set.ncard_singleton] at hup
  exact ⟨A,hAG,by omega,hproper⟩

lemma IsCritical.delete_edge_number {k : ℕ} {G : SimpleGraph V}
    (hG : IsCritical k G) {u v : V} (huv : G.Adj u v) :
    number (G.deleteEdges {s(u,v)}) + 1 = k := by
  obtain ⟨hle,hne,hedge⟩ := delete_edge_properties G huv
  have hlo := hG.2 _ hle hne
  have hup := number_le_restriction_add_edges hle
  rw [hedge,Set.ncard_singleton,hG.1] at hup
  omega

lemma IsCritical.not_even {k : ℕ} {G : SimpleGraph V}
    (hG : IsCritical k G) (hk : 0 < k) : ¬∀ v, Even (G.degree v) := by
  intro he
  have hne : G ≠ ⊥ := by
    intro h
    have hh := hG.1
    rw [h,number_bot] at hh
    omega
  obtain ⟨u,v,huv⟩ := (SimpleGraph.ne_bot_iff_exists_adj).mp hne
  obtain ⟨hle,hneq,hedge⟩ := delete_edge_properties G huv
  have hf : (G \ G.deleteEdges {s(u,v)}).IsAcyclic := by
    apply ForestMixedCompletion.acyclic_of_all_edges_at _ u
    intro a b hab
    have hm : s(a,b) ∈ (G \ G.deleteEdges {s(u,v)}).edgeSet := hab
    rw [hedge,Set.mem_singleton_iff] at hm
    rcases Sym2.eq_iff.mp hm with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  have hh := number_le_of_even_forest_complement hle he hf
  have hl := hG.2 _ hle hneq
  rw [hG.1] at hh
  omega

lemma IsCritical.exists_odd_degree {k : ℕ} {G : SimpleGraph V}
    (hG : IsCritical k G) (hk : 0 < k) : ∃ v, Odd (G.degree v) := by
  have h := hG.not_even hk
  push_neg at h
  obtain ⟨v,hv⟩ := h
  exact ⟨v,Nat.not_even_iff_odd.mp hv⟩

lemma forest_critical (G : SimpleGraph V) (hf : G.IsAcyclic) :
    IsCritical G.edgeSet.ncard G := by
  refine ⟨forest_number G hf,?_⟩
  intro A hAG hne
  rw [forest_number A (hf.anti hAG)]
  exact CountCritical.edges_lt hAG hne

lemma exists_forest_same_rank (G : SimpleGraph V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsAcyclic ∧ graphRank T = graphRank G := by
  obtain ⟨T,_,hm⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (show (⊥ : SimpleGraph V) ≤ G from bot_le) isAcyclic_bot
  refine ⟨T,hm.prop.1,hm.prop.2,?_⟩
  apply RainbowComplements.rank_eq_of_adj_reachable hm.prop.1
  intro u v huv
  rw [reachable_eq_of_maximal_isAcyclic T hm]
  exact huv.reachable

lemma forest_number_eq_rank (G : SimpleGraph V) (hf : G.IsAcyclic) :
    number G = graphRank G := by
  rw [forest_number G hf,BlockRankPotential.forest_rank G hf]
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

lemma IsCritical.rank_lt_of_not_acyclic {k : ℕ} {G : SimpleGraph V}
    (hG : IsCritical k G) (hn : ¬G.IsAcyclic) : graphRank G < k := by
  obtain ⟨T,hTG,hf,hr⟩ := exists_forest_same_rank G
  have hne : T ≠ G := fun h => hn (h ▸ hf)
  have hh := hG.2 T hTG hne
  rwa [forest_number_eq_rank T hf,hr] at hh

/-- For a fixed ambient graph, an exact rank bound on ALL restrictions is
EQUIVALENT to saying that its mixed-count-critical restrictions are forests.
Neither side is asserted unconditionally. -/
lemma rank_bound_iff_critical_forests (G : SimpleGraph V) :
    (∀ A : SimpleGraph V, A ≤ G → number A ≤ graphRank A) ↔
    (∀ A : SimpleGraph V, A ≤ G → ∀ k, IsCritical k A → A.IsAcyclic) := by
  constructor
  · intro hb A hAG k hA
    by_contra hn
    have hlo := hA.rank_lt_of_not_acyclic hn
    have hup := hb A hAG
    rw [hA.1] at hup
    omega
  · intro hf A hAG
    by_cases hz : number A = 0
    · rw [hz]; exact Nat.zero_le _
    · obtain ⟨H,hHA,hH⟩ := extract A (number A) (Nat.pos_of_ne_zero hz) le_rfl
      have hh := forest_number_eq_rank H (hf H (hHA.trans hAG) (number A) hH)
      rw [hH.1] at hh
      exact hh.le.trans (rank_mono hHA)

lemma bound_of_critical_subgraphs (G : SimpleGraph V) (B : ℕ)
    (hb : ∀ A : SimpleGraph V, A ≤ G → ∀ k, IsCritical k A → k ≤ B) :
    number G ≤ B := by
  by_cases hz : number G = 0
  · rw [hz]; exact Nat.zero_le _
  · obtain ⟨A,hAG,hA⟩ := extract G (number G) (Nat.pos_of_ne_zero hz) le_rfl
    exact hb A hAG (number G) hA

/-- Separate cycle pieces from single-edge pieces, retaining exact degree
accounting and the number of edges in the singleton part. -/
lemma split_partition (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hcD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition G D) :
    ∃ (c s : ℕ) (A B : SimpleGraph V),
      c + s = D.card ∧ A ≤ G ∧ B ≤ G ∧ B.edgeFinset.card = s ∧
      (∀ v, G.degree v = A.degree v + B.degree v) ∧
      (∀ v, Even (A.degree v)) ∧ (∀ v, A.degree v ≤ 2*c) := by
  let C := D.filter (fun H => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  let S := D \ C
  have hCD : C ⊆ D := Finset.filter_subset _ _
  have hSD : S ⊆ D := Finset.sdiff_subset
  have hc : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => (Finset.mem_filter.mp hH).2
  have hdC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hCD hH) (hCD hK) hne
  have hdS : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd.1 (hSD hH) (hSD hK) hne
  have hs : ∀ H ∈ S, H.edgeSet.ncard = 1 := by
    intro H hH
    rcases hcD H (hSD hH) with hcy | he
    · have hh : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
        refine ⟨hcy.1,?_⟩
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcy.2 v
      exact ((Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hSD hH,hh⟩)).elim
    · rwa [coe_edgeFinset_card] at he
  refine ⟨C.card,S.card,unionPieces G C,unionPieces G S,?_,
    unionPieces_le G C,unionPieces_le G S,?_,?_,?_,?_⟩
  · have h := Finset.card_sdiff_add_card_eq_card hCD
    dsimp only [S]
    omega
  · rw [unionPieces_edge_card G S hdS,Finset.sum_congr rfl hs]
    simp
  · intro v
    rw [unionPieces_degree G C hdC,unionPieces_degree G S hdS,add_comm]
    exact ((Finset.sum_sdiff hCD).trans (decomposition_degree_sum G D hd v)).symm
  · intro v
    rw [unionPieces_degree G C hdC]
    exact Finset.even_sum _ (fun H hH => regular_two_piece_degree_even H (hc H hH).2 v)
  · intro v
    rw [unionPieces_degree G C hdC]
    calc
      (∑ H ∈ C, H.degree v) ≤ ∑ H ∈ C, 2 := by
        apply Finset.sum_le_sum
        intro H hH
        by_cases hv : v ∈ H.verts
        · have hh := (hc H hH).2 ⟨v,hv⟩
          rw [Subgraph.coe_degree] at hh
          have hh' : H.degree v = 2 := by
            simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
          exact hh'.le
        · simp [Subgraph.degree_of_notMem_verts hv]
      _ = 2*C.card := by simp [mul_comm]

lemma independent_degree_sum_le_edges (G : SimpleGraph V) (S : Finset V)
    (hi : ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v) :
    (∑ v ∈ S, G.degree v) ≤ G.edgeFinset.card := by
  have hd : Set.PairwiseDisjoint (S : Set V) (fun v => G.incidenceFinset v) := by
    intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro e heu hev
    exact hi u hu v hv (G.adj_of_mem_incidenceSet hne
      (G.mem_incidenceFinset u e |>.mp heu) (G.mem_incidenceFinset v e |>.mp hev))
  have hc := Finset.card_biUnion hd
  simp only [card_incidenceFinset_eq_degree] at hc
  rw [← hc]
  apply Finset.card_le_card
  intro e he
  obtain ⟨v,hv,hev⟩ := Finset.mem_biUnion.mp he
  exact G.incidenceFinset_subset v hev

lemma number_le_family_cover {I : Type*} [Fintype I] (G : SimpleGraph V)
    (F : I → G.Subgraph)
    (hc : ∀ i, (F i).coe.Connected ∧ (F i).coe.IsRegularOfDegree 2)
    (hd : Pairwise (fun i j => Disjoint (F i).edgeSet (F j).edgeSet))
    (he : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (F i).edgeSet) :
    number G ≤ Fintype.card I := by
  let D := Finset.univ.image F
  have hcD : ∀ H ∈ D, IsCycleOrEdge H.coe := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    left
    refine ⟨(hc i).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hc i).2 v
  have hdD : IsDecomposition G D := by
    constructor
    · intro H hH K hK hne
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
      exact hd (fun hij => hne (congrArg F hij))
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨H,_,hH⟩
        exact H.edgeSet_subset hH
      · intro hG
        obtain ⟨i,hi⟩ := he e hG
        exact ⟨F i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩
  exact (number_le G D hcD hdD).trans (Finset.card_image_le.trans_eq (Finset.card_univ))

end Erdos184.MixedCritical
