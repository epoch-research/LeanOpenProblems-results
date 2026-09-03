import Submission.FourGraphFamily
import Submission.AllowedFourCounts
import Submission.CanonicalPairAdmissibility

/-! Transferring the four-color numerical catalogue to arbitrary subfamilies,
and excluding zero contacts in a hypothetical optimum-three core. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.FourSubfamilyPatterns
open Critical MaximumCycles MaximumCoreFamilies CycleSegments Subfamilies
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def lowerEquiv {R : SimpleGraph V} (A : Finset G.Subgraph)
    (hcov : (⋃ H ∈ A, H.edgeSet) = R.edgeSet) : A ≃ lowerFamily A hcov :=
  Equiv.ofBijective (fun i => ⟨lowerPiece A hcov i,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨by
      intro i j hij
      exact lowerPiece_injective A hcov (congrArg Subtype.val hij),by
      rintro ⟨H,hH⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hH
      exact ⟨i,Subtype.ext hi⟩⟩

lemma pattern {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (H : Fin 4 → G.Subgraph) (hH : Function.Injective H) (hmem : ∀ i, H i ∈ D) :
    AllowedFourCounts.Pattern (fun P Q : G.Subgraph => (P.verts ∩ Q.verts).ncard) H := by
  let A := Finset.univ.image H
  have hAD : A ⊆ D := by
    intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact hmem i
  have hcA : A.card = 4 := by
    rw [Finset.card_image_of_injective _ hH,Finset.card_univ,Fintype.card_fin]
  let hcov := (subfamilyGraph_edges A).symm
  let E := lowerFamily A hcov
  have hEA : E.card = A.card := lowerFamily_card A hcov
  have hcyc : ∀ K ∈ E, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD.1 i.val (hAD i.property)
  have hdec : IsDecomposition (subfamilyGraph A) E := lowerFamily_decomposition A hcov
    (fun K hK L hL hne => hD.2.1.1 (hAD hK) (hAD hL) hne)
  have hmax : IsMaximum (subfamilyGraph A) E := ⟨hcyc,hdec,by
    intro T hT hdT
    rw [hEA]
    exact hD.subfamily_bound A hAD T hT hdT⟩
  have hdegA (x : V) : (subfamilyGraph A).degree x ≤ 4 :=
    (SimpleGraph.degree_le_of_le (v := x) (subfamilyGraph_le A)).trans (hdeg x)
  have hthreeA : ∀ T ⊆ E, T.card = 3 → number (subfamilyGraph T) ≤ 2 := by
    intro T hTE hcT
    obtain ⟨B,hBA,hcard,hgraph⟩ := FourGraphFamily.lower_subfamily A hcov T hTE
    rw [← hgraph]
    exact hthree B (hBA.trans hAD) (hcard.trans hcT)
  obtain ⟨_,k,hk,e,hcontacts⟩ := FourGraphFamily.number_and_contacts hmax (hEA.trans hcA) hdegA hthreeA
  let g : Fin 4 ≃ A := Equiv.ofBijective (fun i => ⟨H i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨by intro i j hij; exact hH (congrArg Subtype.val hij),by
      rintro ⟨K,hK⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hK
      exact ⟨i,Subtype.ext hi⟩⟩
  let e0 : Fin 4 ≃ E := g.trans (lowerEquiv A hcov)
  let p : Equiv.Perm (Fin 4) := e.trans e0.symm
  have hverts (i : Fin 4) : (e0 i).val.verts = (H i).verts := rfl
  have hmap (i : Fin 4) : e0 (p i) = e i := e0.apply_symm_apply (e i)
  have hv (i : Fin 4) : (H (p i)).verts = (e i).val.verts := by
    rw [← hverts,hmap]
  refine ⟨k,hk,p,?_⟩
  intro i j hij
  change ((H (p i)).verts ∩ (H (p j)).verts).ncard = _
  rw [hv,hv]
  exact hcontacts i j hij

lemma core_pattern {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (T : Fin 4 → D) (hT : Function.Injective T) :
    AllowedFourCounts.Pattern (fun i j : D => (i.val.verts ∩ j.val.verts).ncard) T := by
  have hgt := hD.card_gt_of_nonrigid hr
  rw [hn] at hgt
  have hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2 := by
    intro A hAD hcA
    have hs : A ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hAD,by
      intro hh
      have hc := congrArg Finset.card hh
      omega⟩
    have hlt := proper_subfamily_number_lt hD.1 hD.2.1 hm A hs
    rw [hn] at hlt
    omega
  exact pattern hD (degree_le_four_of_nonrigid_three he hm hn hr) hthree
    (fun i => (T i).val) (Subtype.val_injective.comp hT) (fun i => (T i).property)

lemma core_pair_contact_pos {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (i j : D) (hij : i ≠ j) : 0 < (i.val.verts ∩ j.val.verts).ncard := by
  have hcard := FourGraphFamily.three_core_maximum_ge_five hD he hm hn hr
  have hc : 5 ≤ Fintype.card D := by simpa only [Fintype.card_coe] using hcard
  apply AllowedFourCounts.all_positive (fun i j : D => (i.val.verts ∩ j.val.verts).ncard) hc
    (core_pattern hD he hm hn hr) ?_ i j hij
  intro T hT
  have ht := CanonicalThreeReduction.maximum_triple_of_core hD (by omega) he hm hn hr
    (fun i => (T i).val) (Subtype.val_injective.comp hT) (fun i => (T i).property)
  exact ht.2.2.2.1

lemma core_no_three_doubles {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (T : Fin 4 → D) (hT : Function.Injective T) :
    ¬ (((T 0).val.verts ∩ (T 1).val.verts).ncard = 2 ∧
      ((T 0).val.verts ∩ (T 2).val.verts).ncard = 2 ∧
      ((T 0).val.verts ∩ (T 3).val.verts).ncard = 2) :=
  AllowedFourCounts.no_three_doubles _ (core_pattern hD he hm hn hr T hT)

#print axioms pattern
#print axioms core_pair_contact_pos
#print axioms core_no_three_doubles
end Erdos184Work.FourSubfamilyPatterns
