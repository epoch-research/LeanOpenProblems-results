import Submission.SixCaseCompatibility1
import Submission.PureSixOrbitLookup1
import Submission.PureSixActions1
import Submission.SixRepresentativeCertificates1
import Submission.CyclicRowKernel

/-! Transporting checked six-layout orbit certificates back to canonical rows. -/
namespace Erdos184Work.SixOrbitKernel1
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction LabelKernel Erdos184Serial SixRows1
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma action_rows_eq (o : Orders) {c : ℕ} (hc : PureSixOrbitLookup1.table.lookup (SixRows1.key o) = some c) :
    (PureSixActions1.action (PureSixOrbitLookup1.groupOfCode c)).apply (SixCaseCompatibility1.rawRows o) =
      PureSixRowModel1.unkey (PureSixOrbitLookup1.representativeKey (PureSixOrbitLookup1.representativeOfCode c)) := by
  have hz := PureSixOrbitLookup1.lookup_certificate hc
  change PureSixActions1.actionKey (PureSixOrbitLookup1.groupOfCode c) (SixRows1.key o) =
    PureSixOrbitLookup1.representativeKey (PureSixOrbitLookup1.representativeOfCode c) at hz
  unfold PureSixActions1.actionKey at hz
  rw [SixCaseCompatibility1.unkey_rawRows] at hz
  rw [PureSixActions1.action_apply_eq]
  calc
    _ = PureSixRowModel1.unkey (PureSixRowModel1.key (PureSixActions1.applyRows (PureSixOrbitLookup1.groupOfCode c) (SixCaseCompatibility1.rawRows o))) :=
      (PureSixRowModel1.unkey_key _).symm
    _ = _ := congrArg PureSixRowModel1.unkey hz

lemma classification (o : Orders) (h : LocalBounds b hb o) :
    ∃ r : SixRepresentativeCertificates1.Representatives, r ∈ SixRepresentativeCertificates1.good ∧
      ∃ Q, Partition (code (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o))
        Finset.univ Q ∧ Q.card = 2 := by
  obtain ⟨c,hc⟩ := SixCaseCompatibility1.exists_code o h
  let g := PureSixOrbitLookup1.groupOfCode c
  let r := PureSixOrbitLookup1.representativeOfCode c
  let a := PureSixActions1.action g
  let q := SixCaseCompatibility1.rawRows o
  let M := a.embedding PureSixRowModel1.edge q
  have ha : a.apply q = PureSixRowModel1.unkey (SixRepresentativeCertificates1.representativeKey r) := action_rows_eq o hc
  have hraw : ∀ Q, Partition (code (PureSixRowModel1.src q) (PureSixRowModel1.dst q)) Finset.univ Q → Q.card ≤ 6 := by
    intro Q hQ
    rw [SixCaseCompatibility1.src_rawRows o h,SixCaseCompatibility1.dst_rawRows o h] at hQ
    exact LocalBounds.flat_upper b hb o h Q hQ
  have hiff := M.upper_bound_map_iff Finset.univ 6
  have hmap : (Finset.univ : Finset PureSixRowModel1.E).map M.edge = Finset.univ := a.map_univ PureSixRowModel1.edge q
  rw [hmap] at hiff
  have hout := hiff.mpr hraw
  change ∀ Q, Partition (code (PureSixRowModel1.src (a.apply q)) (PureSixRowModel1.dst (a.apply q)))
    Finset.univ Q → Q.card ≤ 6 at hout
  rw [ha] at hout
  obtain ⟨hr,Q,hQ,hcQ⟩ := SixRepresentativeCertificates1.exists_two_of_upper r hout
  have hQ' : Partition (code (PureSixRowModel1.src (a.apply q)) (PureSixRowModel1.dst (a.apply q)))
      ((Finset.univ : Finset PureSixRowModel1.E).map M.edge) Q := by
    rw [hmap,ha]
    exact hQ
  obtain ⟨S,hS,hcS⟩ := unmap_partition_exists M.edge M.valid_map hQ'
  change Partition (code (PureSixRowModel1.src q) (PureSixRowModel1.dst q)) Finset.univ S at hS
  rw [SixCaseCompatibility1.src_rawRows o h,SixCaseCompatibility1.dst_rawRows o h] at hS
  exact ⟨r,hr,S,hS,hcS.trans hcQ⟩

lemma exists_flat_two (o : Orders) (h : LocalBounds b hb o) :
    ∃ Q, Partition (code (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o))
      Finset.univ Q ∧ Q.card = 2 := by
  obtain ⟨_,_,Q,hQ,hc⟩ := classification o h
  exact ⟨Q,hQ,hc⟩

lemma exists_two (o : Orders) (h : LocalBounds b hb o) :
    ∃ P, Partition (code (source b hb o) (target b hb o)) Finset.univ P ∧ P.card = 2 := by
  obtain ⟨P,hP,hcP⟩ := exists_flat_two o h
  let M := FlatCanonicalKernel.embedding b hb o
  obtain ⟨Q,hQ,hcQ⟩ := map_partition_exists M.edge M.valid_map hP
  rw [FlatCanonicalKernel.map_univ] at hQ
  exact ⟨Q,hQ,hcQ.trans hcP⟩
lemma not_localBounds (o : Orders) : ¬ LocalBounds b hb o := by
  intro h
  obtain ⟨r,hr,_⟩ := classification o h
  simpa only [SixRepresentativeCertificates1.good,Finset.notMem_empty] using hr
#print axioms not_localBounds
#print axioms classification
#print axioms exists_two
end Erdos184Work.SixOrbitKernel1
