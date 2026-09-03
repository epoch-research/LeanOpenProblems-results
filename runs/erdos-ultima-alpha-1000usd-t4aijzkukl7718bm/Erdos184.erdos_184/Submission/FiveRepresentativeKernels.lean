import Submission.FiveKernel0
import Submission.FiveKernel1
import Submission.FiveKernel2
import Submission.FiveKernel3
import Submission.FiveKernel4

/-! Uniform local conclusion for all five numerical representatives.
Transport from an arbitrarily labelled five-color family is a separate step. -/
namespace Erdos184Work.FiveRepresentativeKernels
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalThreeReduction FiveCanonicalCounts
set_option maxHeartbeats 2000000
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma exists_two (k : Fin 5) (o : Orders k)
    (h : LocalBounds (counts k) (marker_bound k) o) :
    ∃ P, Partition (code (source (counts k) (marker_bound k) o)
      (target (counts k) (marker_bound k) o)) Finset.univ P ∧ P.card = 2 := by
  fin_cases k
  · exact FiveRows0.exists_two o h
  · exact FiveRows1.exists_two o h
  · exact FiveRows2.exists_two o h
  · exact FiveRows3.exists_two o h
  · exact FiveRows4.exists_two o h

lemma exists_two_of_eq (k : Fin 5) (b : PairIndex 5 → Fin 3)
    (hb : ∀ i, 2 ≤ (markers b i).card) (he : b = counts k)
    (o : ∀ i, Marked.Order (arity b i)) (h : LocalBounds b hb o) :
    ∃ P, Partition (code (source b hb o) (target b hb o)) Finset.univ P ∧ P.card = 2 := by
  subst b
  exact exists_two k o h

def allowed : Finset (Fin 5) := {0,1,2,3}

lemma allowed_of_bounds (k : Fin 5) (o : Orders k)
    (h : LocalBounds (counts k) (marker_bound k) o) : k ∈ allowed := by
  fin_cases k
  · decide
  · decide
  · decide
  · decide
  · have hh := FiveRows4.catalogue o h
    have hf : False := by simpa only [FiveRows4.good,Finset.notMem_empty] using hh
    exact hf.elim

lemma allowed_of_eq (k : Fin 5) (b : PairIndex 5 → Fin 3)
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
end Erdos184Work.FiveRepresentativeKernels
