import Submission.CanonicalColoredCoarsening

/-! Pulling local color bounds back through an injective kernel relabelling. -/
open scoped Classical
namespace Erdos184Work.ColoredEmbeddingBounds
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening CanonicalThreeReduction
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable local instance coloredBoundsDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma colorLabels_map {I J : Type*} [Fintype I] [Fintype J]
    {m : I → ℕ} {n : J → ℕ}
    (e : (Σ i, Fin (m i)) ≃ (Σ j, Fin (n j))) (T : I ≃ J)
    (hcolor : ∀ a, (e a).1 = T a.1) (A : Finset I) :
    (PathSubstitution.Family.colorLabels A).map e.toEmbedding =
      PathSubstitution.Family.colorLabels (A.map T.toEmbedding) := by
  ext b
  simp only [Finset.mem_map,PathSubstitution.Family.colorLabels,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.1,ha,(hcolor a).symm⟩
  · rintro ⟨i,hi,hb⟩
    refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
    have hc := hcolor (e.symm b)
    rw [e.apply_symm_apply] at hc
    have he : (e.symm b).1 = i := T.injective (hc.symm.trans hb.symm)
    rwa [he]

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
lemma localBounds (hsmall : ∀ i : A, arity b i.val ≤ 4)
    (h : LocalBounds b hb o) : LocalBounds b₀ hb₀ o₀ := by
  constructor
  · intro B D hD
    obtain ⟨E,hE,hcE⟩ := map_partition_exists M.edge M.valid_map hD
    rw [hmap] at hE
    have hu := StableCanonicalCoarsening.local_upper b hb o A hr hsmall h
      (B.map T.toEmbedding) E hE
    rw [Finset.card_map,hcE] at hu
    exact hu
  · intro B hB
    obtain ⟨E,hE,hcE⟩ := StableCanonicalCoarsening.local_three b hb o A hr hsmall h
      (B.map T.toEmbedding) (by simpa only [Finset.card_map] using hB)
    let S := SupportTransport.ofEmbedding M.edge M.valid_map
    have hs := S.exists_partition_card_iff (PathSubstitution.Family.colorLabels B) (fun n => n ≤ 2)
    change (∃ D, Partition _ ((PathSubstitution.Family.colorLabels B).map M.edge) D ∧ _) ↔ _ at hs
    rw [hmap] at hs
    exact hs.mp ⟨E,hE,hcE⟩

#print axioms colorLabels_map
#print axioms localBounds
end Erdos184Work.ColoredEmbeddingBounds
