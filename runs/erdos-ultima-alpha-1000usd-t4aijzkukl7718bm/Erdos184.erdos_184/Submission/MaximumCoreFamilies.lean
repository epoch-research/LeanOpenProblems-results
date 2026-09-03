import Submission.RigidityDegree

/-! Maximum cycle partitions and necessary local conditions for a hypothetical
nonrigid minimal core of optimum three. No such core is constructed, and its
nonexistence is not proved here. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.MaximumCoreFamilies
open Critical EvenCore Rigidity MaximumCycles Subfamilies
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Cycle-only decomposition of greatest cardinality, rather than least. -/
def IsMaximum (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
  IsDecomposition G D ∧
  ∀ E : Finset G.Subgraph,
    (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
    IsDecomposition G E → E.card ≤ D.card

lemma exists_maximum (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph, IsMaximum G D := by
  letI : Fintype G.Subgraph := Fintype.ofFinite _
  let S : Finset (Finset G.Subgraph) := Finset.univ.filter fun D =>
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D
  obtain ⟨A,hA,hdA,_⟩ := minimum_cycles he
  have hS : S.Nonempty := ⟨A,by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using And.intro hA hdA⟩
  obtain ⟨D,hD,hm⟩ := Finset.exists_max_image S Finset.card hS
  have hp := (Finset.mem_filter.mp hD).2
  refine ⟨D,hp.1,hp.2,?_⟩
  intro E hE hdE
  exact hm E (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hE,hdE⟩)

lemma IsMaximum.subfamily_bound {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (A : Finset G.Subgraph) (hAD : A ⊆ D)
    (E : Finset (subfamilyGraph A).Subgraph)
    (hE : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdE : IsDecomposition (subfamilyGraph A) E) : E.card ≤ A.card := by
  obtain ⟨B,hB,hpB,heB,hcB⟩ := lift_cycle_decomposition_exact (subfamilyGraph_le A) E hE hdE
  have hcov : (⋃ H ∈ A, H.edgeSet) = ⋃ H ∈ B, H.edgeSet :=
    (subfamilyGraph_edges A).symm.trans heB.symm
  obtain ⟨E',hE',hdE',hc⟩ := replace_cycle_subfamily_exact D A B hD.1 hD.2.1 hAD hB hpB hcov
  have hm := hD.2.2 E' hE' hdE'
  omega

lemma subfamily_decomposition (A : Finset G.Subgraph)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet)) :
    ∃ E : Finset (subfamilyGraph A).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (subfamilyGraph A) E ∧ E.card = A.card := by
  let hcov := (subfamilyGraph_edges A).symm
  refine ⟨lowerFamily A hcov,?_,lowerFamily_decomposition A hcov hp,lowerFamily_card A hcov⟩
  simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using lowerFamily_property
      (fun H => H.Connected ∧ H.IsRegularOfDegree 2) A hcov (by
        simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hA)

lemma IsMaximum.subfamily_rigid_iff {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (A : Finset G.Subgraph) (hAD : A ⊆ D) :
    CycleRigid (subfamilyGraph A) ↔ number (subfamilyGraph A) = A.card := by
  have hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hne => hD.2.1.1 (hAD hH) (hAD hK) hne
  obtain ⟨E,hE,hdE,hcE⟩ := subfamily_decomposition A (fun H hH => hD.1 H (hAD hH)) hp
  constructor
  · intro hr
    exact (hr E hE hdE).symm.trans hcE
  · intro hn B hB hdB
    have hlo := Critical.number_le B (fun H hH => Or.inl (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hB H hH)) hdB
    have hhi := hD.subfamily_bound A hAD B hB hdB
    omega

lemma proper_subfamily_edges_lt {D : Finset G.Subgraph}
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (A : Finset G.Subgraph) (hAD : A ⊂ D) :
    (subfamilyGraph A).edgeFinset.card < G.edgeFinset.card := by
  have hle := subfamilyGraph_le A
  have hne : subfamilyGraph A ≠ G := by
    obtain ⟨H,hHD,hHA⟩ := Finset.exists_of_ssubset hAD
    obtain ⟨e,heH⟩ := cycle_piece_edgeSet_nonempty H (hD H hHD)
    intro heq
    have heG : e ∈ G.edgeSet := H.edgeSet_subset heH
    rw [← heq,subfamilyGraph_edges] at heG
    obtain ⟨K,hK⟩ := Set.mem_iUnion.mp heG
    obtain ⟨hKA,heK⟩ := Set.mem_iUnion.mp hK
    have hHK : H ≠ K := by rintro rfl; exact hHA hKA
    exact Set.disjoint_left.mp (hd.1 hHD (hAD.1 hKA) hHK) heH heK
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono hle,?_⟩
  exact fun h => hne (SimpleGraph.edgeFinset_inj.mp h)

lemma proper_subfamily_number_lt {D : Finset G.Subgraph}
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hm : EvenMinimal G)
    (A : Finset G.Subgraph) (hAD : A ⊂ D) :
    number (subfamilyGraph A) < number G := by
  apply hm (subfamilyGraph A) (subfamilyGraph_le A)
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      cycle_subfamily_even A (fun H hH => hD H (hAD.1 hH))
        (fun _ hH _ hK hne => hd.1 (hAD.1 hH) (hAD.1 hK) hne)
  · exact proper_subfamily_edges_lt hD hd A hAD

lemma IsMaximum.card_gt_of_nonrigid {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hn : ¬ CycleRigid G) : number G < D.card := by
  by_contra h
  apply hn
  intro E hE hdE
  have hhi := hD.2.2 E hE hdE
  have hlo := Critical.number_le E (fun H hH => Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hE H hH)) hdE
  omega

lemma degree_le_four_of_nonrigid_three (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hn : number G = 3) (hr : ¬ CycleRigid G) (v : V) :
    G.degree v ≤ 4 := by
  have hle := StarCore.number_degree_bound G v
  have hne : G.degree v ≠ 2 * number G := by
    intro h
    exact hr (rigid_of_saturated_evenMinimal he hm v h)
  have heven := Nat.even_iff.mp (he v)
  omega

lemma piece_incidence_count {D : Finset G.Subgraph}
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (v : V) :
    G.degree v = 2 * (D.filter (fun H => v ∈ H.verts)).card := by
  have hg : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hd.2)
  have hs := subfamilyGraph_degree D hd.1 v
  rw [hg] at hs
  rw [hs]
  calc
    (∑ H ∈ D, H.spanningCoe.degree v) = ∑ H ∈ D, if v ∈ H.verts then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      exact regular_two_spanning_degree H (hD H hH).2 v
    _ = 2 * (D.filter (fun H => v ∈ H.verts)).card := by
      simp [Finset.sum_ite,Nat.mul_comm]

/-- Necessary conditions for a hypothetical nonrigid core of optimum three.
The finite layout classification needed to exclude these conditions is not
assumed or proved by this theorem. -/
theorem three_core_maximum_family (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hn : number G = 3) (hr : ¬ CycleRigid G) :
    ∃ D : Finset G.Subgraph,
      IsMaximum G D ∧ 3 < D.card ∧
      (∀ H ∈ D, ∀ K ∈ D, H ≠ K → (H.verts ∩ K.verts).ncard ≤ 2) ∧
      (∀ v, (D.filter (fun H => v ∈ H.verts)).card ≤ 2) ∧
      (∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2) := by
  obtain ⟨D,hD⟩ := exists_maximum G he
  have hcard := hD.card_gt_of_nonrigid hr
  rw [hn] at hcard
  refine ⟨D,hD,hcard,?_,?_,?_⟩
  · intro H hH K hK hne
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2 H K hH hK hne
  · intro v
    have hd := degree_le_four_of_nonrigid_three he hm hn hr v
    have hc := piece_incidence_count hD.1 hD.2.1 v
    omega
  · intro A hAD hA
    have hproper : A ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hAD,by
      intro h
      have hc := congrArg Finset.card h
      omega⟩
    have hlt := proper_subfamily_number_lt hD.1 hD.2.1 hm A hproper
    omega

#print axioms exists_maximum
#print axioms IsMaximum.subfamily_rigid_iff
#print axioms three_core_maximum_family
end Erdos184Work.MaximumCoreFamilies
