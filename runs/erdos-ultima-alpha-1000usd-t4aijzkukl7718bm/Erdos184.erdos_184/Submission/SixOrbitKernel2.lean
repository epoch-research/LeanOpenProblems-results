import Submission.SixCaseCompatibility2
import Submission.PureSixOrbitLookup2
import Submission.PureSixActions2
import Submission.SixRepresentativeCertificates2
import Submission.CyclicRowKernel

/-! Transporting checked six-layout orbit certificates back to canonical rows. -/
namespace Erdos184Work.SixOrbitKernel2
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction LabelKernel Erdos184Serial SixRows2
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma action_rows_eq (o : Orders) {c : ℕ} (hc : PureSixOrbitLookup2.table.lookup (SixRows2.key o) = some c) :
    (PureSixActions2.action (PureSixOrbitLookup2.groupOfCode c)).apply (SixCaseCompatibility2.rawRows o) =
      PureSixRowModel2.unkey (PureSixOrbitLookup2.representativeKey (PureSixOrbitLookup2.representativeOfCode c)) := by
  have hz := PureSixOrbitLookup2.lookup_certificate hc
  change PureSixActions2.actionKey (PureSixOrbitLookup2.groupOfCode c) (SixRows2.key o) =
    PureSixOrbitLookup2.representativeKey (PureSixOrbitLookup2.representativeOfCode c) at hz
  unfold PureSixActions2.actionKey at hz
  rw [SixCaseCompatibility2.unkey_rawRows] at hz
  rw [PureSixActions2.action_apply_eq]
  calc
    _ = PureSixRowModel2.unkey (PureSixRowModel2.key (PureSixActions2.applyRows (PureSixOrbitLookup2.groupOfCode c) (SixCaseCompatibility2.rawRows o))) :=
      (PureSixRowModel2.unkey_key _).symm
    _ = _ := congrArg PureSixRowModel2.unkey hz

lemma classification (o : Orders) (h : LocalBounds b hb o) :
    ∃ r : SixRepresentativeCertificates2.Representatives, r ∈ SixRepresentativeCertificates2.good ∧
      ∃ Q, Partition (code (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o))
        Finset.univ Q ∧ Q.card = 2 := by
  obtain ⟨c,hc⟩ := SixCaseCompatibility2.exists_code o h
  let g := PureSixOrbitLookup2.groupOfCode c
  let r := PureSixOrbitLookup2.representativeOfCode c
  let a := PureSixActions2.action g
  let q := SixCaseCompatibility2.rawRows o
  let M := a.embedding PureSixRowModel2.edge q
  have ha : a.apply q = PureSixRowModel2.unkey (SixRepresentativeCertificates2.representativeKey r) := action_rows_eq o hc
  have hraw : ∀ Q, Partition (code (PureSixRowModel2.src q) (PureSixRowModel2.dst q)) Finset.univ Q → Q.card ≤ 6 := by
    intro Q hQ
    rw [SixCaseCompatibility2.src_rawRows o h,SixCaseCompatibility2.dst_rawRows o h] at hQ
    exact LocalBounds.flat_upper b hb o h Q hQ
  have hiff := M.upper_bound_map_iff Finset.univ 6
  have hmap : (Finset.univ : Finset PureSixRowModel2.E).map M.edge = Finset.univ := a.map_univ PureSixRowModel2.edge q
  rw [hmap] at hiff
  have hout := hiff.mpr hraw
  change ∀ Q, Partition (code (PureSixRowModel2.src (a.apply q)) (PureSixRowModel2.dst (a.apply q)))
    Finset.univ Q → Q.card ≤ 6 at hout
  rw [ha] at hout
  obtain ⟨hr,Q,hQ,hcQ⟩ := SixRepresentativeCertificates2.exists_two_of_upper r hout
  have hQ' : Partition (code (PureSixRowModel2.src (a.apply q)) (PureSixRowModel2.dst (a.apply q)))
      ((Finset.univ : Finset PureSixRowModel2.E).map M.edge) Q := by
    rw [hmap,ha]
    exact hQ
  obtain ⟨S,hS,hcS⟩ := unmap_partition_exists M.edge M.valid_map hQ'
  change Partition (code (PureSixRowModel2.src q) (PureSixRowModel2.dst q)) Finset.univ S at hS
  rw [SixCaseCompatibility2.src_rawRows o h,SixCaseCompatibility2.dst_rawRows o h] at hS
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
  simpa only [SixRepresentativeCertificates2.good,Finset.notMem_empty] using hr
#print axioms not_localBounds
#print axioms classification
#print axioms exists_two
end Erdos184Work.SixOrbitKernel2
