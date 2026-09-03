import Submission.TwoForestAbsorption
import Submission.LongCyclePacking

/-!
An even graph can complete a mixed cycle/edge packing whose uncovered edges
form a forest, without increasing the piece count. In particular, any mixed
partition after deleting a vertex bounds the original pure-cycle minimum.
This does not supply a linear bound for the required mixed partition.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ForestMixedCompletion
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma complete_mixed_packing (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (hf : (G \ unionPieces G D).IsAcyclic) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  let C := D.filter (fun H => H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
  let S := D \ C
  have hCD : C ⊆ D := Finset.filter_subset _ _
  have hSD : S ⊆ D := Finset.sdiff_subset
  have hc : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun _ hH => (Finset.mem_filter.mp hH).2
  have hdC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd (hCD hH) (hCD hK) hne
  have hdS : Set.PairwiseDisjoint (S : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hd (hSD hH) (hSD hK) hne
  have hs : ∀ H ∈ S, H.edgeSet.ncard = 1 := by
    intro H hH
    rcases hD H (hSD hH) with hcy | he
    · have hcy' : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
        refine ⟨hcy.1,?_⟩
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcy.2 v
      exact ((Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hSD hH,hcy'⟩)).elim
    · have hh := coe_edgeFinset_card G H
      simp only [edgeFinset_card,← Nat.card_eq_fintype_card] at he hh
      exact hh.symm.trans he
  have hScard : (unionPieces G S).edgeFinset.card = S.card := by
    calc
      (unionPieces G S).edgeFinset.card = ∑ H ∈ S, H.edgeSet.ncard := by
        simpa only [edgeFinset_card,← Nat.card_eq_fintype_card]
          using unionPieces_edge_card G S hdS
      _ = S.card := by rw [Finset.sum_congr rfl hs]; simp
  let R := G \ unionPieces G C
  have heR : ∀ v, Even (R.degree v) := by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G he C hc hdC v
  have hrem : R \ unionPieces G S = G \ unionPieces G D := by
    apply edgeSet_injective
    simp only [R,edgeSet_sdiff,unionPieces_edgeSet]
    ext e
    simp only [Set.mem_diff,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨heG,hnC⟩,hnS⟩
      refine ⟨heG,?_⟩
      rintro ⟨H,hH,heH⟩
      by_cases hHC : H ∈ C
      · exact hnC ⟨H,hHC,heH⟩
      · exact hnS ⟨H,Finset.mem_sdiff.mpr ⟨hH,hHC⟩,heH⟩
    · rintro ⟨heG,hnD⟩
      exact ⟨⟨heG,fun ⟨H,hH,heH⟩ => hnD ⟨H,hCD hH,heH⟩⟩,
        fun ⟨H,hH,heH⟩ => hnD ⟨H,hSD hH,heH⟩⟩
  obtain ⟨F,hcF,hdF⟩ := even_cycle_decomposition R (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heR v)
  have hF : F.card ≤ S.card := by
    have hh := decomposition_edge_transversal_bound R (unionPieces G S) F hdF
      (fun H hH => TwoForestAbsorption.cycle_hits_marked R (unionPieces G S)
        (by rw [hrem]; exact hf) H (hcF H hH).1 (hcF H hH).2)
    simp only [edgeFinset_card,← Nat.card_eq_fintype_card] at hh hScard
    exact hh.trans_eq hScard
  obtain ⟨E,hcE,hdE,hcardE⟩ := complete_cycle_packing G C hc hdC F (by
    intro H hH
    refine ⟨(hcF H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcF H hH).2 v) hdF
  have hh := Finset.card_sdiff_add_card_eq_card hCD
  exact ⟨E,hcE,hdE,by dsimp only [S] at hF; omega⟩

/-- The existing cycles are retained as a packing. The forest being added
need not be spanning, connected, or have even degrees. -/
lemma extend_mixed_decomposition {G A : SimpleGraph V} (hAG : A ≤ G)
    (he : ∀ v, Even (G.degree v)) (hf : (G \ A).IsAcyclic)
    (D : Finset A.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hd : IsDecomposition A D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  let P := D.image (promote hAG)
  have hp : ∀ H ∈ P, IsCycleOrEdge H.coe := by
    intro H hH
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    rcases hD K hK with hcy | he
    · left
      refine ⟨hcy.1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcy.2 v
    · right
      simpa only [edgeFinset_card,← Nat.card_eq_fintype_card] using he
  have hdis : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) := by
    intro H hH K hK hne
    obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hK
    exact hd.1 hX hY (fun hh => hne (congrArg (promote hAG) hh))
  have hU : unionPieces G P = A := by
    apply edgeSet_injective
    rw [unionPieces_edgeSet,← hd.2]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,hH,heH⟩
      obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      exact ⟨K,hK,heH⟩
    · rintro ⟨K,hK,heK⟩
      exact ⟨promote hAG K,Finset.mem_image.mpr ⟨K,hK,rfl⟩,heK⟩
  obtain ⟨E,hcE,hdE,hcardE⟩ := complete_mixed_packing G he P hp hdis (hU.symm ▸ hf)
  exact ⟨E,hcE,hdE,hcardE.trans Finset.card_image_le⟩

lemma acyclic_of_all_edges_at (B : SimpleGraph V) (v : V)
    (h : ∀ a b, B.Adj a b → a = v ∨ b = v) : B.IsAcyclic := by
  intro a p hp
  have h2 : (p.toSubgraph.neighborSet a).ncard = 2 :=
    hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
  have hex : (p.toSubgraph.neighborSet a).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  obtain ⟨b,hb⟩ := hex
  have hne : a ≠ b := (p.toSubgraph.adj_sub hb).ne
  obtain ⟨w,hw,hwv⟩ : ∃ w ∈ p.support, w ≠ v := by
    by_cases hav : a = v
    · refine ⟨b, ?_, ?_⟩
      · exact p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts a hb)
      · intro hbv; exact hne (hav.trans hbv.symm)
    · exact ⟨a,p.start_mem_support,hav⟩
  have hsub : p.toSubgraph.neighborSet w ⊆ {v} := by
    intro u hu
    exact (h w u (p.toSubgraph.adj_sub hu)).resolve_left hwv
  have hh := Set.ncard_le_ncard hsub
  have hh2 := hp.ncard_neighborSet_toSubgraph_eq_two hw
  simp only [Set.ncard_singleton] at hh
  omega

lemma incidence_complement_acyclic (G : SimpleGraph V) (v : V) :
    (G \ G.deleteIncidenceSet v).IsAcyclic := by
  apply acyclic_of_all_edges_at _ v
  intro a b hab
  by_contra hn
  push_neg at hn
  exact hab.2 (deleteIncidenceSet_adj.mpr ⟨hab.1,hn.1,hn.2⟩)
/-- Deleting all edges at one vertex from an even graph cannot lower its
minimum mixed piece count below the original pure-cycle minimum. -/
lemma extend_from_deleted_vertex (G : SimpleGraph V) (v : V)
    (he : ∀ w, Even (G.degree w))
    (D : Finset (G.deleteIncidenceSet v).Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hd : IsDecomposition (G.deleteIncidenceSet v) D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card ≤ D.card := by
  exact extend_mixed_decomposition (G.deleteIncidenceSet_le v) he
    (incidence_complement_acyclic G v) D hD hd

end Erdos184.ForestMixedCompletion
