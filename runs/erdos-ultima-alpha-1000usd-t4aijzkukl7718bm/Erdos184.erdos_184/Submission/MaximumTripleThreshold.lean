import Submission.SevenGraphFamily

/-! A maximum cycle partition with no rigid triple has optimum at most two.
This is a local threshold theorem, not an arbitrary-optimum rigidity result. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.MaximumTripleThreshold
open Critical Rigidity MaximumCycles MaximumCoreFamilies Subfamilies
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma subfamily_degree (A : Finset G.Subgraph)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hp : Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet)) (v : V) :
    (subfamilyGraph A).degree v = 2 * (A.filter (fun H => v ∈ H.verts)).card := by
  rw [subfamilyGraph_degree A hp]
  calc
    (∑ H ∈ A, H.spanningCoe.degree v) = ∑ H ∈ A, if v ∈ H.verts then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      exact regular_two_spanning_degree H (hA H hH).2 v
    _ = 2 * (A.filter (fun H => v ∈ H.verts)).card := by
      simp [Finset.sum_ite,Nat.mul_comm]

lemma degree_le_four {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2) :
    ∀ v, G.degree v ≤ 4 := by
  intro v
  have hd := piece_incidence_count hD.1 hD.2.1 v
  suffices (D.filter (fun H => v ∈ H.verts)).card ≤ 2 by omega
  by_contra hn
  have hge : 3 ≤ (D.filter (fun H => v ∈ H.verts)).card := by omega
  obtain ⟨A,hA,hcA⟩ := Finset.exists_subset_card_eq hge
  have hAD : A ⊆ D := hA.trans (Finset.filter_subset _ _)
  have hAf : A.filter (fun H => v ∈ H.verts) = A := by
    apply Finset.filter_eq_self.mpr
    intro H hH
    exact (Finset.mem_filter.mp (hA hH)).2
  have hdA := subfamily_degree A (fun H hH => hD.1 H (hAD hH))
    (fun H hH K hK hne => hD.2.1.1 (hAD hH) (hAD hK) hne) v
  rw [hAf,hcA] at hdA
  have hlo := StarCore.number_degree_bound (subfamilyGraph A) v
  have hhi := hthree A hAD hcA
  omega

lemma pair_contact_positive {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : 5 ≤ D.card)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2) :
    ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard := by
  have hdeg := degree_le_four hD hthree
  have hfour (T : Fin 4 → D) (hT : Function.Injective T) :
      AllowedFourCounts.Pattern (fun i j : D => (i.val.verts ∩ j.val.verts).ncard) T :=
    FourSubfamilyPatterns.pattern hD hdeg hthree (fun i => (T i).val)
      (Subtype.val_injective.comp hT) (fun i => (T i).property)
  have htriple (T : Fin 3 → D) (hT : Function.Injective T) :
      2 ≤ ((T 0).val.verts ∩ (T 1).val.verts).ncard +
        ((T 0).val.verts ∩ (T 2).val.verts).ncard := by
    let H : Fin 3 → G.Subgraph := fun i => (T i).val
    have hH : Function.Injective H := Subtype.val_injective.comp hT
    have hmem (i) : H i ∈ D := (T i).property
    have h01 := hH.ne (by decide : (0 : Fin 3) ≠ 1)
    have h02 := hH.ne (by decide : (0 : Fin 3) ≠ 2)
    have h12 := hH.ne (by decide : (1 : Fin 3) ≠ 2)
    have hn : number (subfamilyGraph {H 0,H 1,H 2}) ≤ 2 := by
      apply hthree
      · intro K hK
        simp only [Finset.mem_insert,Finset.mem_singleton] at hK
        rcases hK with rfl | rfl | rfl <;> exact hmem _
      · simp [h01,h02,h12]
    exact (maximum_triple_admissible hD hdeg H hH hmem hn).2.2.2.1
  intro H hH K hK hne
  exact AllowedFourCounts.all_positive (fun i j : D => (i.val.verts ∩ j.val.verts).ncard)
    (by simpa only [Fintype.card_coe] using hcD) hfour htriple
    ⟨H,hH⟩ ⟨K,hK⟩ (fun he => hne (congrArg Subtype.val he))

lemma number_le_two {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2) :
    number G ≤ 2 := by
  have hdeg := degree_le_four hD hthree
  by_cases hsmall : D.card ≤ 2
  · have hn := number_le D (fun H hH => Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hD.1 H hH)) hD.2.1
    omega
  by_cases h3 : D.card = 3
  · have hn := hthree D (Finset.Subset.refl _) h3
    have hg : subfamilyGraph D = G :=
      SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hD.2.1.2)
    rwa [hg] at hn
  by_cases h4 : D.card = 4
  · exact FourGraphFamily.number_le_two hD h4 hdeg hthree
  have hge : 5 ≤ D.card := by omega
  have hpos := pair_contact_positive hD hge hthree
  by_cases h5 : D.card = 5
  · exact FiveGraphFamily.number_le_two hD h5 hdeg hthree hpos
  by_cases h6 : D.card = 6
  · exact SixGraphFamily.number_le_two hD h6 hdeg hthree hpos
  exact (SevenGraphFamily.not_large_family hD (by omega) hdeg hthree hpos).elim

lemma exists_rigid_triple {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hn : 3 ≤ number G) :
    ∃ A ⊆ D, A.card = 3 ∧ CycleRigid (subfamilyGraph A) := by
  by_contra h
  have hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2 := by
    intro A hAD hcA
    have hnot : ¬ CycleRigid (subfamilyGraph A) := fun hr => h ⟨A,hAD,hcA,hr⟩
    have hneq : number (subfamilyGraph A) ≠ A.card :=
      fun he => hnot ((hD.subfamily_rigid_iff A hAD).mpr he)
    obtain ⟨E,hE,hdE,hcE⟩ := subfamily_decomposition A
      (fun H hH => hD.1 H (hAD hH))
      (fun H hH K hK hne => hD.2.1.1 (hAD hH) (hAD hK) hne)
    have hb := number_le E (fun H hH => Or.inl (by simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hE H hH)) hdE
    omega
  have hb := number_le_two hD hthree
  omega

#print axioms degree_le_four
#print axioms number_le_two
#print axioms exists_rigid_triple
end Erdos184Work.MaximumTripleThreshold
