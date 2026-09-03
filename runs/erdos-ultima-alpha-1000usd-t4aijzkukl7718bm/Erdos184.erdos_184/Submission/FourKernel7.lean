import Submission.FourData7

/-! Complete exclusion for this numerical four-color pattern, together with
its necessary catalogue under local subfamily bounds alone. -/
namespace Erdos184Work.FourRows7
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalThreeReduction
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma source_table (o : Orders) (h : LocalBounds b hb o) (e : E) :
    FlatCanonicalKernel.src b hb o e = srcTable (key o) e := by
  rw [src_table_row ⟨key o,key_lt o⟩,digit_key0,digit_key1,digit_key2,digit_key3,flat_src o h]
lemma target_table (o : Orders) (h : LocalBounds b hb o) (e : E) :
    FlatCanonicalKernel.dst b hb o e = dstTable (key o) e := by
  rw [dst_table_row ⟨key o,key_lt o⟩,digit_key0,digit_key1,digit_key2,digit_key3,flat_dst o h]

def witness (o : Orders) : PartitionData E W := lookup (key o)
lemma witness_valid (o : Orders) (h : LocalBounds b hb o) :
    (witness o).Valid (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o) Finset.univ := by
  have hv := table_valid ⟨key o,key_lt o⟩
  have hs := funext (source_table o h)
  have ht := funext (target_table o h)
  rw [← hs,← ht] at hv
  exact hv

lemma witness_size_le (o : Orders) (h : LocalBounds b hb o) : (lookup (key o)).size ≤ 4 := by
  obtain ⟨P,hP,hcP⟩ := PartitionData.exists_partition (witness_valid o h)
  have hu := LocalBounds.flat_upper b hb o h P hP
  change P.card = (lookup (key o)).size at hcP
  omega

lemma catalogue (o : Orders) (h : LocalBounds b hb o) :
    (⟨key o,key_lt o⟩ : Fin 144) ∈ good :=
  (size_mem ⟨key o,key_lt o⟩).mp (witness_size_le o h)

lemma exists_flat_two (o : Orders) (h : LocalBounds b hb o) :
    ∃ P, Partition (code (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o))
      Finset.univ P ∧ P.card = 2 := by
  obtain ⟨P,hP,hcP⟩ := PartitionData.exists_partition (witness_valid o h)
  have hs := size_two ⟨key o,key_lt o⟩ (witness_size_le o h)
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
end Erdos184Work.FourRows7
