import Submission.FlatCanonicalKernel

/-! The subfamily bounds used in the finite analysis, without full-support
minimality or a prescribed full-support minimum. -/
namespace Erdos184Work.CanonicalThreeReduction
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 2000000
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (arity b i))

def LocalBounds : Prop :=
  let C := code (source b hb o) (target b hb o)
  (∀ A : Finset (Fin l), ∀ P,
    Partition C (PathSubstitution.Family.colorLabels A) P → P.card ≤ A.card) ∧
  (∀ A : Finset (Fin l), A.card = 3 → ∃ P,
    Partition C (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ 2)

lemma Restrictions.localBounds (h : Restrictions b hb o) : LocalBounds b hb o :=
  ⟨h.2.2.1,h.2.2.2⟩

lemma LocalBounds.flat_upper (h : LocalBounds b hb o)
    (P : Finset (Finset (Fin (FlatCanonicalKernel.size b))))
    (hP : Partition (code (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o))
      Finset.univ P) : P.card ≤ l := by
  let M := FlatCanonicalKernel.embedding b hb o
  obtain ⟨Q,hQ,hcQ⟩ := map_partition_exists M.edge M.valid_map hP
  rw [FlatCanonicalKernel.map_univ] at hQ
  have hu : PathSubstitution.Family.colorLabels (Finset.univ : Finset (Fin l)) =
      (Finset.univ : Finset (Σ i, Fin (arity b i+2))) := by
    ext e
    simp [PathSubstitution.Family.colorLabels]
  have hm := h.1 Finset.univ Q (hu.symm ▸ hQ)
  simp only [Finset.card_univ,Fintype.card_fin] at hm
  omega

#print axioms LocalBounds.flat_upper
end Erdos184Work.CanonicalThreeReduction
