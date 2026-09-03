import Submission.CanonicalLocalBounds
import Submission.StableCanonicalCoarsening

/-! Canonical coarsening preserves spectra of every color subfamily, not just
of the full selected family. -/
open scoped Classical
namespace Erdos184Work.WordKernel
open Erdos184Serial LabelKernel
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {K W : Type*} [Fintype K] [DecidableEq K] [DecidableEq W] {n : K → ℕ}
noncomputable local instance coloredRestrictionDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
variable (place : ∀ i, Fin (n i+2) → W) (A : Finset K) (B : Finset A)

lemma restrict_colors :
    (Finset.univ.filter (fun e : Σ i : A, Fin (n i.val+2) => e.1 ∈ B)).map (restrictEdge A) =
      Finset.univ.filter (fun e : Σ i : K, Fin (n i+2) => e.1 ∈ B.image Subtype.val) := by
  ext e
  simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j.1,hj,rfl⟩
  · rintro ⟨i,hi,he⟩
    rcases e with ⟨k,j⟩
    change i.val = k at he
    subst k
    exact ⟨⟨i,j⟩,hi,rfl⟩

lemma restriction_color_spectrum (P : ℕ → Prop) :
    (∃ D, Partition (code (source place) (target place))
      (Finset.univ.filter (fun e : Σ i : K, Fin (n i+2) => e.1 ∈ B.image Subtype.val)) D ∧ P D.card) ↔
    (∃ D, Partition (code (source (restrictedPlace place A)) (target (restrictedPlace place A)))
      (Finset.univ.filter (fun e : Σ i : A, Fin (n i.val+2) => e.1 ∈ B)) D ∧ P D.card) := by
  have h := (restrictTransport place A).exists_partition_card_iff
    (Finset.univ.filter (fun e : Σ i : A, Fin (n i.val+2) => e.1 ∈ B)) P
  change (∃ D, Partition _ ((Finset.univ.filter (fun e : Σ i : A, Fin (n i.val+2) => e.1 ∈ B)).map
    (restrictEdge A)) D ∧ _) ↔ _ at h
  rwa [restrict_colors] at h
end Erdos184Work.WordKernel

namespace Erdos184Work.CanonicalSubsetCoarsening
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (arity b i)) (A : Finset (Fin l))
  (hr : ∀ i : A, 2 ≤ (retained b A i.val).card)
noncomputable local instance coloredCanonicalDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma color_spectrum (hsmall : ∀ i : A, arity b i.val ≤ 4)
    (B : Finset A) (P : ℕ → Prop) :
    (∃ D, Partition (code (source b hb o) (target b hb o))
      (PathSubstitution.Family.colorLabels (B.image Subtype.val)) D ∧ P D.card) ↔
    (∃ D, Partition (code (coarseSource b hb o A hr) (coarseTarget b hb o A hr))
      (PathSubstitution.Family.colorLabels B) D ∧ P D.card) := by
  have hres := WordKernel.restriction_color_spectrum (fastWord b hb o) A B P
  have hcoarse := WordCoarsening.color_spectrum_iff (wordEmbedding b hb o A) (keep b hb o A)
    (keep_lower b hb o A hr)
    (fun i => CyclicSeries.valid (hsmall i) (keep b hb o A i) (keep_lower b hb o A hr i))
    (removed_private b hb o A) B P
  have hs : source b hb o = WordKernel.source (fastWord b hb o) := source_eq_fast b hb o
  have ht : target b hb o = WordKernel.target (fastWord b hb o) := target_eq_fast b hb o
  rw [hs,ht]
  have hlarge : PathSubstitution.Family.colorLabels (m := fun i => arity b i+2)
      (B.image Subtype.val) = Finset.univ.filter (fun e : Σ i, Fin (arity b i+2) =>
        e.1 ∈ B.image Subtype.val) := by
    ext e
    simp [PathSubstitution.Family.colorLabels]
  have hlocal : PathSubstitution.Family.colorLabels (m := fun i : A =>
      WordCoarsening.arity (keep b hb o A) i+2) B =
      Finset.univ.filter (fun e : Σ i : A, Fin (WordCoarsening.arity (keep b hb o A) i+2) =>
        e.1 ∈ B) := by
    ext e
    simp [PathSubstitution.Family.colorLabels]
  rw [hlarge,hlocal]
  exact hres.trans hcoarse

#print axioms color_spectrum
end Erdos184Work.CanonicalSubsetCoarsening

namespace Erdos184Work.StableCanonicalCoarsening
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (CanonicalPairLayout.arity b i)) (A : Finset (Fin l))
  (hr : ∀ i : A, 2 ≤ (retained b A i.val).card)
noncomputable local instance coloredStableDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma map_colors (B : Finset A) :
    (PathSubstitution.Family.colorLabels (m := fun i => arity b A i+2) B).map
      (embedding b hb o A hr).edge = PathSubstitution.Family.colorLabels B := by
  ext e
  simp only [Finset.mem_map,PathSubstitution.Family.colorLabels,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact hj
  · intro he
    rcases e with ⟨i,r⟩
    refine ⟨⟨i,(index b hb o A i).symm r⟩,he,?_⟩
    change (⟨i,index b hb o A i ((index b hb o A i).symm r)⟩ :
      Σ i : A, Fin (WordCoarsening.arity (keep b hb o A) i+2)) = ⟨i,r⟩
    rw [Equiv.apply_symm_apply]

lemma color_spectrum (hsmall : ∀ i : A, CanonicalPairLayout.arity b i.val ≤ 4)
    (B : Finset A) (P : ℕ → Prop) :
    (∃ D, Partition (code (CanonicalPairKernel.source b hb o) (CanonicalPairKernel.target b hb o))
      (PathSubstitution.Family.colorLabels (B.image Subtype.val)) D ∧ P D.card) ↔
    (∃ D, Partition (code (source b hb o A hr) (target b hb o A hr))
      (PathSubstitution.Family.colorLabels B) D ∧ P D.card) := by
  let M := embedding b hb o A hr
  let T := SupportTransport.ofEmbedding M.edge M.valid_map
  have h := T.exists_partition_card_iff (PathSubstitution.Family.colorLabels B) P
  change (∃ D, Partition _ ((PathSubstitution.Family.colorLabels B).map M.edge) D ∧ _) ↔ _ at h
  rw [map_colors] at h
  exact (CanonicalSubsetCoarsening.color_spectrum b hb o A hr hsmall B P).trans h

lemma local_upper (hsmall : ∀ i : A, CanonicalPairLayout.arity b i.val ≤ 4)
    (h : CanonicalThreeReduction.LocalBounds b hb o)
    (B : Finset A) (D : Finset (Finset (Σ i : A, Fin (arity b A i+2))))
    (hD : Partition (code (source b hb o A hr) (target b hb o A hr))
      (PathSubstitution.Family.colorLabels B) D) : D.card ≤ B.card := by
  obtain ⟨E,hE,hcE⟩ := (color_spectrum b hb o A hr hsmall B (fun n => n = D.card)).mpr ⟨D,hD,rfl⟩
  have hu := h.1 (B.image Subtype.val) E hE
  rw [Finset.card_image_of_injective _ Subtype.val_injective,hcE] at hu
  exact hu

lemma local_three (hsmall : ∀ i : A, CanonicalPairLayout.arity b i.val ≤ 4)
    (h : CanonicalThreeReduction.LocalBounds b hb o)
    (B : Finset A) (hB : B.card = 3) :
    ∃ D, Partition (code (source b hb o A hr) (target b hb o A hr))
      (PathSubstitution.Family.colorLabels B) D ∧ D.card ≤ 2 := by
  apply (color_spectrum b hb o A hr hsmall B (fun n => n ≤ 2)).mp
  exact h.2 _ (by rw [Finset.card_image_of_injective _ Subtype.val_injective,hB])

#print axioms color_spectrum
#print axioms local_upper
#print axioms local_three
end Erdos184Work.StableCanonicalCoarsening
