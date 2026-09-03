import Submission.FourKernel0
import Submission.FourKernel1
import Submission.FourKernel2
import Submission.FourKernel3
import Submission.FourKernel4
import Submission.FourKernel5
import Submission.FourKernel6
import Submission.FourKernel7
import Submission.FourKernel8

/-! Uniform local conclusion for all nine numerical representatives.
Transport from an arbitrarily labelled four-color family is a separate step. -/
namespace Erdos184Work.FourRepresentativeKernels
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalThreeReduction FourCanonicalCounts
set_option maxHeartbeats 2000000
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma exists_two (k : Fin 9) (o : Orders k)
    (h : LocalBounds (counts k) (marker_bound k) o) :
    ∃ P, Partition (code (source (counts k) (marker_bound k) o)
      (target (counts k) (marker_bound k) o)) Finset.univ P ∧ P.card = 2 := by
  fin_cases k
  · exact FourRows0.exists_two o h
  · exact FourRows1.exists_two o h
  · exact FourRows2.exists_two o h
  · exact FourRows3.exists_two o h
  · exact FourRows4.exists_two o h
  · exact FourRows5.exists_two o h
  · exact FourRows6.exists_two o h
  · exact FourRows7.exists_two o h
  · exact FourRows8.exists_two o h

lemma exists_two_of_eq (k : Fin 9) (b : PairIndex 4 → Fin 3)
    (hb : ∀ i, 2 ≤ (markers b i).card) (he : b = counts k)
    (o : ∀ i, Marked.Order (arity b i)) (h : LocalBounds b hb o) :
    ∃ P, Partition (code (source b hb o) (target b hb o)) Finset.univ P ∧ P.card = 2 := by
  subst b
  exact exists_two k o h

def allowed : Finset (Fin 9) := {0,2,3,4,6}

lemma allowed_of_bounds (k : Fin 9) (o : Orders k)
    (h : LocalBounds (counts k) (marker_bound k) o) : k ∈ allowed := by
  fin_cases k
  · decide
  · have hh := FourRows1.catalogue o h
    have hf : False := by simpa only [FourRows1.good,Finset.notMem_empty] using hh
    exact hf.elim
  · decide
  · decide
  · decide
  · have hh := FourRows5.catalogue o h
    have hf : False := by simpa only [FourRows5.good,Finset.notMem_empty] using hh
    exact hf.elim
  · decide
  · have hh := FourRows7.catalogue o h
    have hf : False := by simpa only [FourRows7.good,Finset.notMem_empty] using hh
    exact hf.elim
  · have hh := FourRows8.catalogue o h
    have hf : False := by simpa only [FourRows8.good,Finset.notMem_empty] using hh
    exact hf.elim

lemma allowed_of_eq (k : Fin 9) (b : PairIndex 4 → Fin 3)
    (hb : ∀ i, 2 ≤ (markers b i).card) (he : b = counts k)
    (o : ∀ i, Marked.Order (arity b i)) (h : LocalBounds b hb o) : k ∈ allowed := by
  subst b
  exact allowed_of_bounds k o h

lemma not_restrictions (k : Fin 9) (o : Orders k) :
    ¬ Restrictions (counts k) (marker_bound k) o := by
  intro h
  obtain ⟨P,hP,hcP⟩ := exists_two k o (Restrictions.localBounds _ _ _ h)
  have hlo := h.1.1.2 P hP
  omega

#print axioms allowed_of_bounds
#print axioms exists_two
#print axioms not_restrictions
end Erdos184Work.FourRepresentativeKernels
