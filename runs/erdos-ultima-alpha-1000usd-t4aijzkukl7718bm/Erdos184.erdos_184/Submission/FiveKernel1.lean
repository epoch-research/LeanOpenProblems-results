import Submission.FiveCertificates1
import Submission.FiveCaseSelection1

/-! Exclusion of a canonical optimum-three core in this five-color pattern.
This finite result does not establish an arbitrary-core bound. -/
namespace Erdos184Work.FiveRows1
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalThreeReduction
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

noncomputable def witness (o : Orders) (h : LocalBounds b hb o) : PartitionData E W := data (index o h)
lemma witness_valid (o : Orders) (h : LocalBounds b hb o) :
    (witness o h).Valid (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o) Finset.univ := by
  have hs : caseSource (index o h) = FlatCanonicalKernel.src b hb o := by
    funext e
    unfold caseSource
    rw [index_key,digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact (flat_src o h e).symm
  have ht : caseTarget (index o h) = FlatCanonicalKernel.dst b hb o := by
    funext e
    unfold caseTarget
    rw [index_key,digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact (flat_dst o h e).symm
  change (data (index o h)).Valid _ _ Finset.univ
  rw [← hs,← ht]
  exact data_valid (index o h)

lemma witness_size_le (o : Orders) (h : LocalBounds b hb o) : (witness o h).size ≤ 5 := by
  obtain ⟨P,hP,hcP⟩ := PartitionData.exists_partition (witness_valid o h)
  have hu := LocalBounds.flat_upper b hb o h P hP
  change P.card = (witness o h).size at hcP
  omega

lemma catalogue (o : Orders) (h : LocalBounds b hb o) :
    (⟨key o,key_lt o⟩ : Fin 3888) ∈ good := by
  have hg := (data_size (index o h) (witness_size_le o h)).2
  have he : (⟨caseKey (index o h),caseKey_lt (index o h)⟩ : Fin 3888) =
      ⟨key o,key_lt o⟩ := Fin.ext (index_key o h)
  rw [← he]
  exact hg

lemma exists_flat_two (o : Orders) (h : LocalBounds b hb o) :
    ∃ P, Partition (code (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o))
      Finset.univ P ∧ P.card = 2 := by
  obtain ⟨P,hP,hcP⟩ := PartitionData.exists_partition (witness_valid o h)
  have hs := (data_size (index o h) (witness_size_le o h)).1
  exact ⟨P,hP,hcP.trans hs⟩

lemma exists_two (o : Orders) (h : LocalBounds b hb o) :
    ∃ P, Partition (code (source b hb o) (target b hb o)) Finset.univ P ∧ P.card = 2 := by
  obtain ⟨P,hP,hcP⟩ := exists_flat_two o h
  let M := FlatCanonicalKernel.embedding b hb o
  obtain ⟨Q,hQ,hcQ⟩ := map_partition_exists M.edge M.valid_map hP
  rw [FlatCanonicalKernel.map_univ] at hQ
  exact ⟨Q,hQ,hcQ.trans hcP⟩

lemma not_restrictions (o : Orders) : ¬ Restrictions b hb o := by
  intro h
  obtain ⟨P,hP,hcP⟩ := exists_two o (Restrictions.localBounds b hb o h)
  have hlo := h.1.1.2 P hP
  omega

#print axioms catalogue
#print axioms exists_two
#print axioms not_restrictions
end Erdos184Work.FiveRows1
