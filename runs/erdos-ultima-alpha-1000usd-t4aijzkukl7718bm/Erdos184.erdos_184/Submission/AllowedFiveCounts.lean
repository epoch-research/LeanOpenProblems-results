import Submission.FiveGraphFamily
import Submission.PureSixDoubleTransfer

/-! Allowed five-contact patterns and the six-color count reduction for graph families.
All conclusions still concern hypothetical nonrigid optimum-three cores. -/
namespace Erdos184Work.AllowedFiveCounts
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
local instance allowedFivePermFintype : Fintype (Equiv.Perm (Fin 5)) := fintypePerm

abbrev value := FiveNumericalPatterns.between
abbrev pairCoords := PureSixDoublePatterns.fivePairCoords
lemma pair_ne : ∀ q : Fin 10, (pairCoords q).1 ≠ (pairCoords q).2 := by decide +kernel
lemma double_count_valid : ∀ k : Fin 5, k ∈ FiveRepresentativeKernels.allowed →
    ∀ p : Equiv.Perm (Fin 5),
    (Finset.univ.filter (fun q : Fin 10 =>
      value (FiveNumericalPatterns.representative k) (p (pairCoords q).1) (p (pairCoords q).2) = 2)).card ≤ 2 := by
  decide +kernel

variable {I : Type*}
def Pattern (a : I → I → ℕ) (T : Fin 5 → I) : Prop :=
  ∃ k : Fin 5, k ∈ FiveRepresentativeKernels.allowed ∧ ∃ p : Equiv.Perm (Fin 5),
    ∀ i j, i ≠ j → a (T (p i)) (T (p j)) = value (FiveNumericalPatterns.representative k) i j

lemma pattern_count_le (a : I → I → ℕ) {T : Fin 5 → I} (h : Pattern a T) :
    (Finset.univ.filter (fun q : Fin 10 => a (T (pairCoords q).1) (T (pairCoords q).2) = 2)).card ≤ 2 := by
  obtain ⟨k,hk,p,hp⟩ := h
  have he (i j : Fin 5) (hij : i ≠ j) :
      a (T i) (T j) = value (FiveNumericalPatterns.representative k) (p.symm i) (p.symm j) := by
    have hh := hp (p.symm i) (p.symm j) (p.symm.injective.ne hij)
    simpa only [p.apply_symm_apply] using hh
  have hh := double_count_valid k hk p.symm
  have hf :
      Finset.univ.filter (fun q : Fin 10 => a (T (pairCoords q).1) (T (pairCoords q).2) = 2) =
      Finset.univ.filter (fun q : Fin 10 =>
        value (FiveNumericalPatterns.representative k) (p.symm (pairCoords q).1) (p.symm (pairCoords q).2) = 2) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [he _ _ (pair_ne q)]
  rwa [hf]

#print axioms pattern_count_le
end Erdos184Work.AllowedFiveCounts

open SimpleGraph
open scoped Classical
namespace Erdos184Work.FiveSubfamilyPatterns
open Critical MaximumCycles MaximumCoreFamilies CycleSegments Subfamilies
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma allowed_pattern {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (hdeg : ∀ x, G.degree x ≤ 4)
    (hthree : ∀ A ⊆ D, A.card = 3 → number (subfamilyGraph A) ≤ 2)
    (hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard)
    (H : Fin 5 → G.Subgraph) (hH : Function.Injective H) (hmem : ∀ i, H i ∈ D) :
    AllowedFiveCounts.Pattern (fun P Q : G.Subgraph => (P.verts ∩ Q.verts).ncard) H := by
  let A := Finset.univ.image H
  have hAD : A ⊆ D := by
    intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact hmem i
  have hcA : A.card = 5 := by
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
  have hposA : ∀ H ∈ E, ∀ K ∈ E, H ≠ K → 0 < (H.verts ∩ K.verts).ncard := by
    intro H hH K hK hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
    exact hpos i.val (hAD i.property) j.val (hAD j.property) (by
      intro he
      exact hne (congrArg (lowerPiece A hcov) (Subtype.ext he)))
  obtain ⟨_,k,hk,e,hcontacts⟩ := FiveGraphFamily.number_and_contacts hmax (hEA.trans hcA) hdegA hthreeA hposA
  let g : Fin 5 ≃ A := Equiv.ofBijective (fun i => ⟨H i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨by intro i j hij; exact hH (congrArg Subtype.val hij),by
      rintro ⟨K,hK⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hK
      exact ⟨i,Subtype.ext hi⟩⟩
  let e0 : Fin 5 ≃ E := g.trans (FourSubfamilyPatterns.lowerEquiv A hcov)
  let p : Equiv.Perm (Fin 5) := e.trans e0.symm
  have hverts (i : Fin 5) : (e0 i).val.verts = (H i).verts := rfl
  have hmap (i : Fin 5) : e0 (p i) = e i := e0.apply_symm_apply (e i)
  have hv (i : Fin 5) : (H (p i)).verts = (e i).val.verts := by
    rw [← hverts,hmap]
  refine ⟨k,hk,p,?_⟩
  intro i j hij
  change ((H (p i)).verts ∩ (H (p j)).verts).ncard = _
  rw [hv,hv]
  exact hcontacts i j hij

lemma core_allowed_pattern {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (T : Fin 5 → D) (hT : Function.Injective T) :
    AllowedFiveCounts.Pattern (fun i j : D => (i.val.verts ∩ j.val.verts).ncard) T := by
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
  have hpos : ∀ H ∈ D, ∀ K ∈ D, H ≠ K → 0 < (H.verts ∩ K.verts).ncard := by
    intro H hH K hK hne
    exact FourSubfamilyPatterns.core_pair_contact_pos hD he hm hn hr ⟨H,hH⟩ ⟨K,hK⟩
      (fun hh => hne (congrArg Subtype.val hh))
  exact allowed_pattern hD (degree_le_four_of_nonrigid_three he hm hn hr) hthree hpos
    (fun i => (T i).val) (Subtype.val_injective.comp hT) (fun i => (T i).property)

lemma core_five_count_bound {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (T : Fin 5 → D) (hT : Function.Injective T) :
    (Finset.univ.filter (fun q : Fin 10 =>
      ((T (AllowedFiveCounts.pairCoords q).1).val.verts ∩
        (T (AllowedFiveCounts.pairCoords q).2).val.verts).ncard = 2)).card ≤ 2 :=
  AllowedFiveCounts.pattern_count_le _ (core_allowed_pattern hD he hm hn hr T hT)

#print axioms core_allowed_pattern
#print axioms core_five_count_bound
end Erdos184Work.FiveSubfamilyPatterns

namespace Erdos184Work.SixSubfamilyPatterns
open Critical MaximumCycles MaximumCoreFamilies
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma core_pattern {D : Finset G.Subgraph} (hD : IsMaximum G D)
    (he : ∀ v, Even (G.degree v)) (hm : EvenCore.EvenMinimal G)
    (hn : number G = 3) (hr : ¬ Rigidity.CycleRigid G)
    (T : Fin 6 → D) (hT : Function.Injective T) :
    ∃ k : Fin 5, ∃ p : Equiv.Perm (Fin 6), ∀ i j, i ≠ j →
      ((T (p i)).val.verts ∩ (T (p j)).val.verts).ncard =
        PureSixDoublePatterns.between (PureSixDoublePatterns.representative k) i j := by
  apply PureSixDoublePatterns.classified_nat
    (fun i j => ((T i).val.verts ∩ (T j).val.verts).ncard)
  · intro i j
    rw [Set.inter_comm]
  · intro i j hij
    exact FourSubfamilyPatterns.core_pair_contact_pos hD he hm hn hr _ _ (hT.ne hij)
  · intro i j hij
    exact maximum_decomposition_intersection_le_two D hD.1 hD.2.1 hD.2.2
      _ _ (T i).property (T j).property (fun h => hij (hT (Subtype.ext h)))
  · intro v
    exact FiveSubfamilyPatterns.core_five_count_bound hD he hm hn hr
      (T ∘ PureSixDoublePatterns.omitColor v) (hT.comp (PureSixDoublePatterns.omitColor_injective v))

#print axioms core_pattern
end Erdos184Work.SixSubfamilyPatterns
