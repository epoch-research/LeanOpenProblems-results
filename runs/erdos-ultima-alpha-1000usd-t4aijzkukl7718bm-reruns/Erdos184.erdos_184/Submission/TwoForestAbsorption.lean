import Submission.ParityCompletion
import Submission.HamiltonReduction
import Submission.MarkedMinimum

/-!
A connected marked subgraph can absorb an unmarked graph that is a union
of two forests. The two-forest hypothesis is essential to this proof and
is not established for arbitrary chord graphs.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TwoForestAbsorption

variable {V : Type*} [Fintype V]

lemma cycle_hits_marked (G R : SimpleGraph V) (hf : (G \ R).IsAcyclic)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2) :
    (H.edgeSet ∩ R.edgeSet).Nonempty := by
  obtain ⟨e,he,hn⟩ := cycle_has_edge_outside_forest (G \ R) hf H hc hr
  refine ⟨e,he,?_⟩
  have hG := H.edgeSet_subset he
  rw [SimpleGraph.edgeSet_sdiff] at hn
  simpa only [Set.mem_diff,hG,true_and,not_not] using hn

lemma combine_hitting (G R A : SimpleGraph V) (hAG : A ≤ G)
    (DA : Finset A.Subgraph) (DC : Finset (G \ A).Subgraph)
    (hcA : ∀ H ∈ DA, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hcC : ∀ H ∈ DC, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdA : IsDecomposition A DA) (hdC : IsDecomposition (G \ A) DC)
    (hhA : ∀ H ∈ DA, (H.edgeSet ∩ R.edgeSet).Nonempty)
    (hhC : ∀ H ∈ DC, (H.edgeSet ∩ R.edgeSet).Nonempty) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ D.card ≤ R.edgeFinset.card := by
  let hCG : G \ A ≤ G := sdiff_le
  let D := DA.image (promote hAG) ∪ DC.image (promote hCG)
  have hdis : Disjoint A.edgeSet (G \ A).edgeSet := by
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hcA K hK).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcA K hK).2 v
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      refine ⟨(hcC K hK).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using (hcC K hK).2 v
  have hh : ∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty := by
    intro H hH
    rcases Finset.mem_union.mp hH with hH | hH
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      exact hhA K hK
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
      exact hhC K hK
  have hd : IsDecomposition G D := by
    constructor
    · intro H hH K hK hne
      rcases Finset.mem_union.mp hH with hH | hH <;>
        rcases Finset.mem_union.mp hK with hK | hK
      · obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
        obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hK
        exact hdA.1 hX hY (fun h => hne (congrArg (promote hAG) h))
      · obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
        obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hK
        exact hdis.mono X.edgeSet_subset Y.edgeSet_subset
      · obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
        obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hK
        exact hdis.symm.mono X.edgeSet_subset Y.edgeSet_subset
      · obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp hH
        obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hK
        exact hdC.1 hX hY (fun h => hne (congrArg (promote hCG) h))
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨H,_,he⟩
        exact H.edgeSet_subset he
      · intro he
        by_cases ha : e ∈ A.edgeSet
        · rw [← hdA.2] at ha
          obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp ha
          exact ⟨promote hAG H,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨H,hH,rfl⟩),heH⟩
        · have heC : e ∈ (G \ A).edgeSet := by
            rw [SimpleGraph.edgeSet_sdiff]
            exact ⟨he,ha⟩
          rw [← hdC.2] at heC
          obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp heC
          exact ⟨promote hCG H,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨H,hH,rfl⟩),heH⟩
  exact ⟨D,hc,hd,hh,decomposition_edge_transversal_bound G R D hd hh⟩

/-- Split a finite even graph into two even parts, with acyclic unmarked
parts, by completing one forest's parity inside a connected marked graph. -/
theorem hitting_of_two_forests (G R F : SimpleGraph V) (hRG : R ≤ G)
    (hR : R.Connected) (he : ∀ v, Even (G.degree v))
    (hF : F ≤ G \ R) (hf : F.IsAcyclic) (hf' : ((G \ R) \ F).IsAcyclic) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ D.card ≤ R.edgeFinset.card := by
  obtain ⟨X,hXR,hpar⟩ := ParityCompletion.exists_parity_subgraph R F hR
  let A := X ⊔ F
  have hAG : A ≤ G := sup_le (hXR.trans hRG) (hF.trans sdiff_le)
  have hdis : Disjoint X.edgeSet F.edgeSet := by
    rw [Set.disjoint_left]
    intro e hx hf
    have hr := SimpleGraph.edgeSet_mono hXR hx
    have hh := SimpleGraph.edgeSet_mono hF hf
    rw [SimpleGraph.edgeSet_sdiff] at hh
    exact hh.2 hr
  have heA : ∀ v, Even (A.degree v) := by
    intro v
    have hdeg : A.degree v = X.degree v + F.degree v := by
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using degree_sup_of_edge_disjoint X F hdis v
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [hdeg,Nat.cast_add,hpar v,CharTwo.add_self_eq_zero]
  have heC : ∀ v, Even ((G \ A).degree v) := by
    intro v
    have hdeg := degree_sdiff_of_le hAG v
    have hG := he v
    have hA := heA v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg hG hA ⊢
    rw [hdeg]
    obtain ⟨a,ha⟩ := hG
    obtain ⟨b,hb⟩ := hA
    exact ⟨a-b,by omega⟩
  have hfA : (A \ R).IsAcyclic := by
    apply SimpleGraph.IsAcyclic.anti (G' := F) _ hf
    intro u v h
    rcases h.1 with hx | hfuv
    · exact (h.2 (hXR hx)).elim
    · exact hfuv
  have hfC : ((G \ A) \ R).IsAcyclic := by
    apply SimpleGraph.IsAcyclic.anti (G' := (G \ R) \ F) _ hf'
    intro u v h
    exact ⟨⟨h.1.1,h.2⟩,fun hfuv => h.1.2 (Or.inr hfuv)⟩
  obtain ⟨DA,hcA,hdA⟩ := even_cycle_decomposition A (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heA v)
  obtain ⟨DC,hcC,hdC⟩ := even_cycle_decomposition (G \ A) (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heC v)
  refine combine_hitting G R A hAG DA DC ?_ ?_ hdA hdC ?_ ?_
  · intro H hH
    refine ⟨(hcA H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcA H hH).2 v
  · intro H hH
    refine ⟨(hcC H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcC H hH).2 v
  · intro H hH
    apply cycle_hits_marked A R hfA H (hcA H hH).1
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcA H hH).2 v
  · intro H hH
    apply cycle_hits_marked (G \ A) R hfC H (hcC H hH).1
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcC H hH).2 v

lemma acyclic_of_degree_le_one (B : SimpleGraph V) (hd : ∀ v, B.degree v ≤ 1) :
    B.IsAcyclic := by
  intro v p hp
  have h2 : p.toSubgraph.degree v = 2 := by
    rw [Subgraph.degree, ← Nat.card_eq_fintype_card]
    exact hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
  have hle := p.toSubgraph.degree_le v
  have hv := hd v
  simp only [Subgraph.degree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at h2 hle hv
  omega

/-- A graph consisting of vertex-disjoint cycles is the union of a
spanning forest and an acyclic remainder of maximum degree one. -/
lemma two_forests_of_isCycles (B : SimpleGraph V) (hb : B.IsCycles) :
    ∃ F : SimpleGraph V, F ≤ B ∧ F.IsAcyclic ∧ (B \ F).IsAcyclic := by
  obtain ⟨F,_,hm⟩ := exists_maximal_isAcyclic_of_le_isAcyclic
    (show (⊥ : SimpleGraph V) ≤ B from bot_le) isAcyclic_bot
  have hFB : F ≤ B := hm.prop.1
  have hreach := reachable_eq_of_maximal_isAcyclic F hm
  refine ⟨F,hFB,hm.prop.2,?_⟩
  apply acyclic_of_degree_le_one
  intro v
  have hdeg : (B \ F).degree v = B.degree v - F.degree v := by
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using degree_sdiff_of_le hFB v
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg ⊢
  rw [hdeg]
  by_cases hex : ∃ w, B.Adj v w
  · obtain ⟨w,hw⟩ := hex
    have hB2 : B.degree v = 2 := by
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq] using hb ⟨w,hw⟩
    have hpath : F.Reachable v w := by rw [hreach]; exact hw.reachable
    have hpos := (F.degree_pos_iff_mem_support v).mpr (mem_support_of_reachable hw.ne hpath)
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hB2 hpos
    omega
  · have hz : B.degree v = 0 := by
      by_contra hh
      exact hex ((B.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hh))
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hz
    omega

/-- This settles the marked-hitting assertion when the entire unmarked
part consists of vertex-disjoint cycles. It does not assume any particular
current cycle decomposition or any local-chain repair rule. -/
theorem hitting_of_blue_cycles (G R : SimpleGraph V) (hRG : R ≤ G)
    (hR : R.Connected) (he : ∀ v, Even (G.degree v)) (hb : (G \ R).IsCycles) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ D.card ≤ R.edgeFinset.card := by
  obtain ⟨F,hF,hf,hf'⟩ := two_forests_of_isCycles (G \ R) hb
  exact hitting_of_two_forests G R F hRG hR he hF hf hf'

/-- In particular, the Hamilton-cycle hitting assertion holds for every
even graph of maximum degree at most four. The arbitrary-degree version
needed for Erdos 184 remains unproved. -/
theorem hitting_of_regular_two_and_max_degree_four (G R : SimpleGraph V)
    (hRG : R ≤ G) (hR : R.Connected) (hrr : R.IsRegularOfDegree 2)
    (he : ∀ v, Even (G.degree v)) (hmax : ∀ v, G.degree v ≤ 4) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧
      (∀ H ∈ D, (H.edgeSet ∩ R.edgeSet).Nonempty) ∧ D.card ≤ Fintype.card V := by
  have hb : (G \ R).IsCycles := by
    intro v hv
    have hpos := (degree_pos_iff_nonempty (G := G \ R) (v := v)).mpr hv
    have hdeg := degree_sdiff_of_le hRG v
    have hR2 := hrr v
    have hGmax := hmax v
    have hGeven := he v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] at hpos hdeg hR2 hGmax hGeven
    obtain ⟨a,ha⟩ := hGeven
    omega
  obtain ⟨D,hc,hd,hh,hbD⟩ := hitting_of_blue_cycles G R hRG hR he hb
  refine ⟨D,hc,hd,hh,?_⟩
  have hcard := regular_two_graph_edge_card R hrr
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hcard hbD ⊢
  omega

/-- The earlier minimum-bad-count optimization has value zero under these
hypotheses. This conclusion is global, not a local chain-repair assumption. -/
theorem minimum_bad_empty_of_blue_cycles (G R : SimpleGraph V) (hRG : R ≤ G)
    (hR : R.Connected) (he : ∀ v, Even (G.degree v)) (hb : (G \ R).IsCycles)
    (D : Finset G.Subgraph)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → (badPieces R D).card ≤ (badPieces R E).card) :
    badPieces R D = ∅ := by
  obtain ⟨E,hcE,hdE,hhE,_⟩ := hitting_of_blue_cycles G R hRG hR he hb
  have hbadE : badPieces R E = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro H hH
    obtain ⟨hHE,hdis⟩ := Finset.mem_filter.mp hH
    exact Set.not_disjoint_iff.mpr (hhE H hHE) hdis
  have hh := hm E hcE hdE
  rw [hbadE,Finset.card_empty] at hh
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)

end Erdos184.TwoForestAbsorption
