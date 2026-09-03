import Submission.StarHullBoost

/-! Every minimum decomposition of a nonempty globally edge-minimal graph
has at least one eighth of its supported vertex count as singleton pieces.
This controls the number of vertices, not the total number of pieces, and
therefore does not establish a uniform linear decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MinimalSingletons
open Critical MaximumCycles Subfamilies EdgeHull
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

lemma proper_hull_lt {G E : SimpleGraph V} (hm : Minimal G) (hEG : E ≤ G) (hne : E ≠ G) :
    value E < number G := by
  obtain ⟨R,hRE,hn⟩ := exists_maximizer E
  have hRG := hRE.trans hEG
  have hRne : R ≠ G := by
    intro h
    apply hne
    apply le_antisymm hEG
    simpa only [h] using hRE
  have hh := hm R hRG hRne
  omega

lemma even_support_gap {G E : SimpleGraph V} (hm : Minimal G) (hEG : E ≤ G) (hne : E ≠ G)
    (hE : ∀ v, Even (Nat.card (E.neighborSet v))) :
    6 * number E + E.support.ncard + 6 ≤ 6 * number G := by
  have hb := StarHullBoost.supported_order_boost E hE
  have hh := proper_hull_lt hm hEG hne
  omega

lemma minimum_split {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) (hc : D.card = number G) :
    ∃ E F : SimpleGraph V, E ≤ G ∧ (∀ v, Even (Nat.card (E.neighborSet v))) ∧
      E ⊔ F = G ∧ number E + (edgePieces D).card = number G ∧
      F.edgeFinset.card = (edgePieces D).card := by
  let A := edgePieces D
  let C := D \ A
  let E := subfamilyGraph C
  let F := subfamilyGraph A
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hCD : C ⊆ D := Finset.sdiff_subset
  have hC : ∀ H ∈ C, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases hD H (hCD hH) with hcy | hed
    · simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hcy
    · exact ((Finset.mem_sdiff.mp hH).2 (Finset.mem_filter.mpr ⟨hCD hH,hed⟩)).elim
  have hEc := cycle_subfamily_even C hC
    (fun _ hH _ hK hne => hdec.1 (hCD hH) (hCD hK) hne)
  have hunion : E ⊔ F = G := by
    change C.sup SimpleGraph.Subgraph.spanningCoe ⊔ A.sup SimpleGraph.Subgraph.spanningCoe = G
    rw [← Finset.sup_union,show C ∪ A = D from Finset.sdiff_union_of_subset hAD]
    exact SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hdec.2)
  have hn : number E = C.card := minimal_subfamily_number D hD hdec hc C hCD
  have hsum : C.card + A.card = D.card := Finset.card_sdiff_add_card_eq_card hAD
  refine ⟨E,F,subfamilyGraph_le C,?_,hunion,by change number E + A.card = number G; omega,
    edgePieces_graph_card D hdec⟩
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hEc v

lemma support_card_le_twice_edges (G : SimpleGraph V) :
    G.support.ncard ≤ 2 * G.edgeFinset.card := by
  have hd (v : V) (hv : v ∈ G.support.toFinset) : 1 ≤ G.degree v :=
    (G.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv)
  have hs := Finset.sum_le_sum (s := G.support.toFinset) (fun v hv => hd v hv)
  have he := G.sum_degrees_support_eq_twice_card_edges
  rw [he] at hs
  simpa only [Finset.sum_const,smul_eq_mul,mul_one,Set.ncard_eq_toFinset_card'] using hs

lemma support_sup_le (E F : SimpleGraph V) :
    (E ⊔ F).support.ncard ≤ E.support.ncard + F.support.ncard := by
  have hs : (E ⊔ F).support ⊆ E.support ∪ F.support := by
    rintro v ⟨w,hvw⟩
    exact hvw.elim (fun h => Or.inl ⟨w,h⟩) (fun h => Or.inr ⟨w,h⟩)
  exact (Set.ncard_le_ncard hs).trans (Set.ncard_union_le _ _)

lemma singleton_count_supported {G : SimpleGraph V} (hm : Minimal G) (hne : G ≠ ⊥)
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hc : D.card = number G) :
    G.support.ncard + 6 ≤ 8 * (edgePieces D).card := by
  obtain ⟨E,F,hEG,hE,hunion,hnum,hFcard⟩ := minimum_split D hD hdec hc
  have hproper : E ≠ G := by
    intro heq
    apply hne
    apply hm.edgeCritical.eq_bot_of_even
    intro v
    have he := hE v
    simpa only [heq,← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he
  have hg := even_support_gap hm hEG hproper hE
  have hf := support_card_le_twice_edges F
  have hs := support_sup_le E F
  rw [hunion] at hs
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hf hFcard
  omega

/-- The cycle-supported order alone gives the stronger factor-six inequality. -/
lemma singleton_count_cycle_support {G : SimpleGraph V} (hm : Minimal G) (hne : G ≠ ⊥)
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hdec : IsDecomposition G D) (hc : D.card = number G) :
    (subfamilyGraph (D \ edgePieces D)).support.ncard + 6 ≤ 6 * (edgePieces D).card := by
  let E := subfamilyGraph (D \ edgePieces D)
  have hEG : E ≤ G := subfamilyGraph_le _
  have hC : ∀ H ∈ D \ edgePieces D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases hD H (Finset.mem_sdiff.mp hH).1 with hcy | hed
    · simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hcy
    · exact ((Finset.mem_sdiff.mp hH).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hH).1,hed⟩)).elim
  have hE : ∀ v, Even (Nat.card (E.neighborSet v)) := by
    have he := cycle_subfamily_even (D \ edgePieces D) hC
      (fun _ hH _ hK hne => hdec.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne)
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he
  have hproper : E ≠ G := by
    intro heq
    apply hne
    apply hm.edgeCritical.eq_bot_of_even
    simpa only [heq,← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hE
  have hg := even_support_gap hm hEG hproper hE
  have hn := minimal_subfamily_number D hD hdec hc (D \ edgePieces D) Finset.sdiff_subset
  have hs := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun H : G.Subgraph =>
    H.coe.edgeFinset.card = 1) D)
  change number E = (D \ edgePieces D).card at hn
  change (D \ edgePieces D).card + (edgePieces D).card = D.card at hs
  change E.support.ncard + 6 ≤ _
  omega

end Erdos184Work.MinimalSingletons
#print axioms Erdos184Work.MinimalSingletons.singleton_count_supported
#print axioms Erdos184Work.MinimalSingletons.singleton_count_cycle_support
