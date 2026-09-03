import Submission.SixGraphFamily

/-! Six-color bounds force every pair contact to be a singleton. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SixContactUniformity
open Critical MaximumCoreFamilies MaximumCycles
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma zero_between : ∀ i j : Fin 6, i ≠ j →
    PureSixDoublePatterns.between (PureSixDoublePatterns.representative 0) i j = 1 := by decide +kernel

lemma contacts_eq_one {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : D.card = 6) (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard) :
    ∀ H ∈ D, ∀ K ∈ D, H ≠ K → (H.verts ∩ K.verts).ncard = 1 := by
  obtain ⟨_,k,hk,e,hc⟩ := SixGraphFamily.number_and_contacts hD hcD hdeg hthree hpos
  have hk0 : k = 0 := by
    simpa only [SixRepresentativeKernels.allowed,Finset.mem_singleton] using hk
  subst k
  intro H hH K hK hne
  have huv : (⟨H,hH⟩ : D) ≠ ⟨K,hK⟩ := fun h => hne (congrArg Subtype.val h)
  have hij := e.symm.injective.ne huv
  have hh := (hc (e.symm ⟨H,hH⟩) (e.symm ⟨K,hK⟩) hij).trans
    (zero_between _ _ hij)
  simpa only [e.apply_symm_apply] using hh

lemma subfamily_contacts_eq_one {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard)
    (A : Finset G.Subgraph) (hAD : A ⊆ D) (hcA : A.card = 6) :
    ∀ H ∈ A, ∀ K ∈ A, H ≠ K → (H.verts ∩ K.verts).ncard = 1 := by
  let hcov := (subfamilyGraph_edges A).symm
  let E := Subfamilies.lowerFamily A hcov
  have hEA : E.card = A.card := Subfamilies.lowerFamily_card A hcov
  have hcyc : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD.1 i.val (hAD i.property)
  have hdec : IsDecomposition (subfamilyGraph A) E :=
    Subfamilies.lowerFamily_decomposition A hcov
      (fun H hH K hK hne => hD.2.1.1 (hAD hH) (hAD hK) hne)
  have hmax : IsMaximum (subfamilyGraph A) E := ⟨hcyc,hdec,by
    intro T hT hdT
    rw [hEA]
    exact hD.subfamily_bound A hAD T hT hdT⟩
  have hdeg' (x : V) : (subfamilyGraph A).degree x ≤ 4 :=
    (SimpleGraph.degree_le_of_le (v := x) (subfamilyGraph_le A)).trans (hdeg x)
  have hthree' : ∀ T ⊆ E, T.card = 3 → number (subfamilyGraph T) ≤ 2 := by
    intro T hTE hcT
    obtain ⟨B,hBA,hcard,hgraph⟩ := FourGraphFamily.lower_subfamily A hcov T hTE
    rw [← hgraph]
    exact hthree B (hBA.trans hAD) (hcard.trans hcT)
  have hpos' : ∀ H ∈ E, ∀ K ∈ E, H ≠ K → 0 < (H.verts ∩ K.verts).ncard := by
    intro H hH K hK hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
    exact hpos i.val (hAD i.property) j.val (hAD j.property) (by
      intro he
      exact hne (congrArg (Subfamilies.lowerPiece A hcov) (Subtype.ext he)))
  have hc := contacts_eq_one hmax (hEA.trans hcA) hdeg' hthree' hpos'
  intro H hH K hK hne
  have hm (i : A) : Subfamilies.lowerPiece A hcov i ∈ E :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  exact hc _ (hm ⟨H,hH⟩) _ (hm ⟨K,hK⟩) (by
    intro he
    have hh := Subfamilies.lowerPiece_injective A hcov he
    exact hne (congrArg Subtype.val hh))

lemma contacts_eq_one_of_ge_six {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hcD : 6 ≤ D.card) (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard) :
    ∀ H ∈ D, ∀ K ∈ D, H ≠ K → (H.verts ∩ K.verts).ncard = 1 := by
  intro H hH K hK hne
  have hpair : ({H,K} : Finset G.Subgraph) ⊆ D := by
    intro L hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl
    · exact hH
    · exact hK
  obtain ⟨A,hpA,hAD,hcA⟩ := Finset.exists_subsuperset_card_eq hpair
    (show ({H,K} : Finset G.Subgraph).card ≤ 6 by simp [hne]) hcD
  exact subfamily_contacts_eq_one hD hdeg hthree hpos A hAD hcA H
    (hpA (by simp)) K (hpA (by simp)) hne

#print axioms contacts_eq_one_of_ge_six
end Erdos184Work.SixContactUniformity
