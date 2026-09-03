import Submission.CanonicalPairLayout

/-! Exact transport to computable pair-slot kernels with canonical marker placement. -/
open scoped Classical
namespace Erdos184Work.CanonicalPairKernel
open PairJunctionCoding JunctionPairCoding PairSlotMarkers CycleSegments
open LabelKernel Erdos184Serial CanonicalPairLayout
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {l : ℕ}

-- These functions depend only on the finite multiplicities and cyclic orders.
def source (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
    (o : ∀ i, Marked.Order (arity b i)) : (Σ i, Fin (arity b i+2)) → Fin ((l*l)*2) :=
  NormalizedKernel.src (place b hb) o

def target (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
    (o : ∀ i, Marked.Order (arity b i)) : (Σ i, Fin (arity b i+2)) → Fin ((l*l)*2) :=
  NormalizedKernel.dst (place b hb) o

section Actual
variable {V : Type*} [Fintype V] (B : Fin l → Set V)
    (htwo : ∀ w : Junction B, Nat.card {i : Fin l // w.val ∈ B i} = 2)
    (hbound : ∀ i j : Fin l, i ≠ j → (B i ∩ B j).ncard ≤ 2)
    (hcontacts : ∀ i, 2 ≤ Fintype.card (LocalJunction B i))
    (o : ∀ i, Marked.Order (arity (counts B htwo hbound) i))

noncomputable local instance {m : Fin l → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

noncomputable def vertexEmbedding :
    Embedding (NormalizedKernel.src (actualPlace B htwo hbound hcontacts) o)
      (NormalizedKernel.dst (actualPlace B htwo hbound hcontacts) o)
      (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
      (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o) where
  edge := Function.Embedding.refl _
  vertex := codeVertex B htwo hbound
  endpoints j := by
    change s(codeVertex B htwo hbound (actualPlace B htwo hbound hcontacts j.1
        ((SmallOrderNormalization.normalized _ (o j.1)).vertex j.2)),
      codeVertex B htwo hbound (actualPlace B htwo hbound hcontacts j.1
        ((SmallOrderNormalization.normalized _ (o j.1)).vertex
          (j.2+(1 : Fin (arity (counts B htwo hbound) j.1+2)))))) = _
    rw [actualPlace_code,actualPlace_code]
    rfl

lemma vertex_map (s : Finset (Σ i, Fin (arity (counts B htwo hbound) i+2))) :
    s.map (vertexEmbedding B htwo hbound hcontacts o).edge = s :=
  Finset.map_refl

lemma normalized_number_iff (k : ℕ) :
    HasNumber (code (NormalizedKernel.src (actualPlace B htwo hbound hcontacts) o)
      (NormalizedKernel.dst (actualPlace B htwo hbound hcontacts) o)) Finset.univ k ↔
    HasNumber (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
      (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)) Finset.univ k := by
  have h := (vertexEmbedding B htwo hbound hcontacts o).hasNumber_map_iff Finset.univ k
  rw [vertex_map] at h
  exact h.symm

lemma normalized_minimal_iff (k : ℕ) :
    MinimalCore (code (NormalizedKernel.src (actualPlace B htwo hbound hcontacts) o)
      (NormalizedKernel.dst (actualPlace B htwo hbound hcontacts) o)) Finset.univ k ↔
    MinimalCore (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
      (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)) Finset.univ k := by
  have h := (vertexEmbedding B htwo hbound hcontacts o).minimalCore_map_iff Finset.univ k
  rw [vertex_map] at h
  exact h.symm

lemma normalized_rigid_iff (k : ℕ) :
    Rigid (code (NormalizedKernel.src (actualPlace B htwo hbound hcontacts) o)
      (NormalizedKernel.dst (actualPlace B htwo hbound hcontacts) o)) Finset.univ k ↔
    Rigid (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
      (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)) Finset.univ k := by
  have h := (vertexEmbedding B htwo hbound hcontacts o).rigid_map_iff Finset.univ k
  rw [vertex_map] at h
  exact h.symm

lemma normalized_upper_iff (A : Finset (Fin l)) (k : ℕ) :
    (∀ P, Partition (code (NormalizedKernel.src (actualPlace B htwo hbound hcontacts) o)
      (NormalizedKernel.dst (actualPlace B htwo hbound hcontacts) o))
      (PathSubstitution.Family.colorLabels A) P → P.card ≤ k) ↔
    (∀ P, Partition
      (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
        (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o))
      (PathSubstitution.Family.colorLabels A) P → P.card ≤ k) := by
  have h := (vertexEmbedding B htwo hbound hcontacts o).upper_bound_map_iff
    (PathSubstitution.Family.colorLabels A) k
  rw [vertex_map] at h
  exact h.symm

lemma normalized_exists_iff (A : Finset (Fin l)) (k : ℕ) :
    (∃ P, Partition (code (NormalizedKernel.src (actualPlace B htwo hbound hcontacts) o)
      (NormalizedKernel.dst (actualPlace B htwo hbound hcontacts) o))
      (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ k) ↔
    (∃ P, Partition
      (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
        (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o))
      (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ k) := by
  constructor
  · rintro ⟨P,hP,hc⟩
    obtain ⟨Q,hQ,hcq⟩ := map_partition_exists (vertexEmbedding B htwo hbound hcontacts o).edge
      (vertexEmbedding B htwo hbound hcontacts o).valid_map hP
    rw [vertex_map] at hQ
    exact ⟨Q,hQ,hcq.trans_le hc⟩
  · rintro ⟨P,hP,hc⟩
    rw [← vertex_map B htwo hbound hcontacts o (PathSubstitution.Family.colorLabels A)] at hP
    obtain ⟨Q,hQ,hcq⟩ := unmap_partition_exists (vertexEmbedding B htwo hbound hcontacts o).edge
      (vertexEmbedding B htwo hbound hcontacts o).valid_map hP
    exact ⟨Q,hQ,hcq.trans_le hc⟩

lemma recursive_minimal_iff (k : ℕ) :
    MinimalCore (code (fun j : Σ i, Fin (arity (counts B htwo hbound) i+2) =>
      actualPlace B htwo hbound hcontacts j.1 j.2)
      (successorDest (n := arity (counts B htwo hbound)) (actualPlace B htwo hbound hcontacts) o))
      Finset.univ k ↔
    MinimalCore (code (source (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)
      (target (counts B htwo hbound) (marker_card_lower B htwo hbound hcontacts) o)) Finset.univ k :=
  (NormalizedKernel.minimal_univ_iff (actualPlace B htwo hbound hcontacts) o k).trans
    (normalized_minimal_iff B htwo hbound hcontacts o k)

#print axioms normalized_minimal_iff
#print axioms normalized_exists_iff
end Actual
end Erdos184Work.CanonicalPairKernel
