import Submission.CyclicSeriesLarger
import Submission.ColoredEmbeddingBounds

/-! Color-subfamily transport allowing up to eight positions per cyclic row.
All original bounded transport APIs remain unchanged. -/
open scoped Classical
namespace Erdos184Work.CanonicalSubsetCoarsening
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (arity b i)) (A : Finset (Fin l))
  (hr : ∀ i : A, 2 ≤ (retained b A i.val).card)
noncomputable local instance largerColoredCanonicalDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma color_spectrum_large (hsmall : ∀ i : A, arity b i.val ≤ 6)
    (B : Finset A) (P : ℕ → Prop) :
    (∃ D, Partition (code (source b hb o) (target b hb o))
      (PathSubstitution.Family.colorLabels (B.image Subtype.val)) D ∧ P D.card) ↔
    (∃ D, Partition (code (coarseSource b hb o A hr) (coarseTarget b hb o A hr))
      (PathSubstitution.Family.colorLabels B) D ∧ P D.card) := by
  have hres := WordKernel.restriction_color_spectrum (fastWord b hb o) A B P
  have hcoarse := WordCoarsening.color_spectrum_iff (wordEmbedding b hb o A) (keep b hb o A)
    (keep_lower b hb o A hr)
    (fun i => CyclicSeries.valid_le_six (hsmall i) (keep b hb o A i) (keep_lower b hb o A hr i))
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

#print axioms color_spectrum_large
end Erdos184Work.CanonicalSubsetCoarsening

namespace Erdos184Work.StableCanonicalCoarsening
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (CanonicalPairLayout.arity b i)) (A : Finset (Fin l))
  (hr : ∀ i : A, 2 ≤ (retained b A i.val).card)
noncomputable local instance largerColoredStableDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma color_spectrum_large (hsmall : ∀ i : A, CanonicalPairLayout.arity b i.val ≤ 6)
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
  exact (CanonicalSubsetCoarsening.color_spectrum_large b hb o A hr hsmall B P).trans h

lemma local_upper_large (hsmall : ∀ i : A, CanonicalPairLayout.arity b i.val ≤ 6)
    (h : CanonicalThreeReduction.LocalBounds b hb o)
    (B : Finset A) (D : Finset (Finset (Σ i : A, Fin (arity b A i+2))))
    (hD : Partition (code (source b hb o A hr) (target b hb o A hr))
      (PathSubstitution.Family.colorLabels B) D) : D.card ≤ B.card := by
  obtain ⟨E,hE,hcE⟩ := (color_spectrum_large b hb o A hr hsmall B (fun n => n = D.card)).mpr ⟨D,hD,rfl⟩
  have hu := h.1 (B.image Subtype.val) E hE
  rw [Finset.card_image_of_injective _ Subtype.val_injective,hcE] at hu
  exact hu

lemma local_three_large (hsmall : ∀ i : A, CanonicalPairLayout.arity b i.val ≤ 6)
    (h : CanonicalThreeReduction.LocalBounds b hb o)
    (B : Finset A) (hB : B.card = 3) :
    ∃ D, Partition (code (source b hb o A hr) (target b hb o A hr))
      (PathSubstitution.Family.colorLabels B) D ∧ D.card ≤ 2 := by
  apply (color_spectrum_large b hb o A hr hsmall B (fun n => n ≤ 2)).mp
  exact h.2 _ (by rw [Finset.card_image_of_injective _ Subtype.val_injective,hB])

#print axioms color_spectrum_large
#print axioms local_upper_large
#print axioms local_three_large
end Erdos184Work.StableCanonicalCoarsening

namespace Erdos184Work.ColoredEmbeddingBounds
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening CanonicalThreeReduction
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable local instance largerColoredBoundsDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

variable {r l : ℕ}
  (b₀ : PairIndex r → Fin 3) (hb₀ : ∀ i, 2 ≤ (markers b₀ i).card)
  (o₀ : ∀ i, Marked.Order (arity b₀ i))
  (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (arity b i)) (A : Finset (Fin l))
  (hr : ∀ i : A, 2 ≤ (retained b A i.val).card)
  (T : Fin r ≃ A)
  (M : Embedding (source b₀ hb₀ o₀) (target b₀ hb₀ o₀)
    (StableCanonicalCoarsening.source b hb o A hr)
    (StableCanonicalCoarsening.target b hb o A hr))
  (hmap : ∀ B : Finset (Fin r), (PathSubstitution.Family.colorLabels B).map M.edge =
    PathSubstitution.Family.colorLabels (B.map T.toEmbedding))

include hr T M hmap in
lemma localBounds_large (hsmall : ∀ i : A, arity b i.val ≤ 6)
    (h : LocalBounds b hb o) : LocalBounds b₀ hb₀ o₀ := by
  constructor
  · intro B D hD
    obtain ⟨E,hE,hcE⟩ := map_partition_exists M.edge M.valid_map hD
    rw [hmap] at hE
    have hu := StableCanonicalCoarsening.local_upper_large b hb o A hr hsmall h
      (B.map T.toEmbedding) E hE
    rw [Finset.card_map,hcE] at hu
    exact hu
  · intro B hB
    obtain ⟨E,hE,hcE⟩ := StableCanonicalCoarsening.local_three_large b hb o A hr hsmall h
      (B.map T.toEmbedding) (by simpa only [Finset.card_map] using hB)
    let S := SupportTransport.ofEmbedding M.edge M.valid_map
    have hs := S.exists_partition_card_iff (PathSubstitution.Family.colorLabels B) (fun n => n ≤ 2)
    change (∃ D, Partition _ ((PathSubstitution.Family.colorLabels B).map M.edge) D ∧ _) ↔ _ at hs
    rw [hmap] at hs
    exact hs.mp ⟨E,hE,hcE⟩

#print axioms localBounds_large
end Erdos184Work.ColoredEmbeddingBounds
