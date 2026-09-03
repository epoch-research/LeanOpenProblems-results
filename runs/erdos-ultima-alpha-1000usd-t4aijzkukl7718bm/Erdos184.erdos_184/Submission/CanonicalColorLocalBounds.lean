import Submission.ColoredKernelLocalBounds
import Submission.CanonicalLocalBounds

/-! The canonical local restrictions in a color-labelled form, before and after flattening. -/
namespace Erdos184Work.CanonicalThreeReduction
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 1000000
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

variable {l : ℕ} (b : PairIndex l → Fin 3) (hb : ∀ i, 2 ≤ (markers b i).card)
  (o : ∀ i, Marked.Order (arity b i))

lemma localBounds_iff_colored : LocalBounds b hb o ↔
    ColorLocalBounds (source b hb o) (target b hb o) Sigma.fst := by
  have he (A : Finset (Fin l)) :
      colorSet (Sigma.fst : (Σ i, Fin (arity b i+2)) → Fin l) A =
        PathSubstitution.Family.colorLabels A := by
    ext e
    simp [colorSet,PathSubstitution.Family.colorLabels]
  simp only [LocalBounds,ColorLocalBounds,he]

lemma LocalBounds.flat_colored (h : LocalBounds b hb o) :
    ColorLocalBounds (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o)
      (FlatCanonicalKernel.color b) := by
  have hc := (localBounds_iff_colored b hb o).mp h
  exact hc.pullback (FlatCanonicalKernel.edge b) (Equiv.refl _)
    (FlatCanonicalKernel.embedding b hb o) rfl (fun _ => rfl)

lemma localBounds_of_flat_colored
    (h : ColorLocalBounds (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o)
      (FlatCanonicalKernel.color b)) : LocalBounds b hb o := by
  apply (localBounds_iff_colored b hb o).mpr
  exact h.transport (FlatCanonicalKernel.edge b) (Equiv.refl _)
    (FlatCanonicalKernel.embedding b hb o) rfl (fun _ => rfl)

#print axioms LocalBounds.flat_colored
#print axioms localBounds_of_flat_colored
end Erdos184Work.CanonicalThreeReduction
