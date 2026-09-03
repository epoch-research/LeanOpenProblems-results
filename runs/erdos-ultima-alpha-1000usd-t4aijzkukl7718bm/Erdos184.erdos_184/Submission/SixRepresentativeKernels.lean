import Submission.SixOrbitKernel0
import Submission.SixOrbitKernel1
import Submission.SixOrbitKernel2
import Submission.SixCaseCompatibility3
import Submission.SixCaseCompatibility4

/-! Uniform six-color local conclusion. It does not settle arbitrary minimal cores. -/
namespace Erdos184Work.SixRepresentativeKernels
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction LabelKernel Erdos184Serial SixCanonicalCounts
set_option maxHeartbeats 3000000
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma exists_two (k : Fin 5) (o : Orders k) (h : LocalBounds (counts k) (marker_bound k) o) :
    ∃ P, Partition (code (source (counts k) (marker_bound k) o)
      (target (counts k) (marker_bound k) o)) Finset.univ P ∧ P.card = 2 := by
  fin_cases k
  · exact SixOrbitKernel0.exists_two o h
  · exact SixOrbitKernel1.exists_two o h
  · exact SixOrbitKernel2.exists_two o h
  · exact (SixCaseCompatibility3.not_localBounds o h).elim
  · exact (SixCaseCompatibility4.not_localBounds o h).elim

lemma exists_two_of_eq (k : Fin 5) (b : PairIndex 6 → Fin 3)
    (hb : ∀ i, 2 ≤ (markers b i).card) (he : b = counts k)
    (o : ∀ i, Marked.Order (arity b i)) (h : LocalBounds b hb o) :
    ∃ P, Partition (code (source b hb o) (target b hb o)) Finset.univ P ∧ P.card = 2 := by
  subst b
  exact exists_two k o h

def allowed : Finset (Fin 5) := {0}

lemma allowed_of_bounds (k : Fin 5) (o : Orders k) (h : LocalBounds (counts k) (marker_bound k) o) :
    k ∈ allowed := by
  fin_cases k
  · decide
  · exact (SixOrbitKernel1.not_localBounds o h).elim
  · exact (SixOrbitKernel2.not_localBounds o h).elim
  · exact (SixCaseCompatibility3.not_localBounds o h).elim
  · exact (SixCaseCompatibility4.not_localBounds o h).elim

lemma allowed_of_eq (k : Fin 5) (b : PairIndex 6 → Fin 3)
    (hb : ∀ i, 2 ≤ (markers b i).card) (he : b = counts k)
    (o : ∀ i, Marked.Order (arity b i)) (h : LocalBounds b hb o) : k ∈ allowed := by
  subst b
  exact allowed_of_bounds k o h

lemma not_restrictions (k : Fin 5) (o : Orders k) :
    ¬ Restrictions (counts k) (marker_bound k) o := by
  intro h
  obtain ⟨P,hP,hcP⟩ := exists_two k o (Restrictions.localBounds _ _ _ h)
  have hlo := h.1.1.2 P hP
  omega

#print axioms allowed_of_bounds
#print axioms exists_two
#print axioms not_restrictions
end Erdos184Work.SixRepresentativeKernels
