import Submission.SixCaseCompatibility0
import Submission.PureSixOrbitLookup0
import Submission.PureSixActions0
import Submission.SixRepresentativeCertificates0
import Submission.CyclicRowKernel

/-! Transporting checked six-layout orbit certificates back to canonical rows. -/
namespace Erdos184Work.SixOrbitKernel0
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction LabelKernel Erdos184Serial SixRows0
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma action_rows_eq (o : Orders) {c : ℕ} (hc : PureSixOrbitLookup0.table.lookup (SixRows0.key o) = some c) :
    (PureSixActions0.action (PureSixOrbitLookup0.groupOfCode c)).apply (SixCaseCompatibility0.rawRows o) =
      PureSixRowModel0.unkey (PureSixOrbitLookup0.representativeKey (PureSixOrbitLookup0.representativeOfCode c)) := by
  have hz := PureSixOrbitLookup0.lookup_certificate hc
  change PureSixActions0.actionKey (PureSixOrbitLookup0.groupOfCode c) (SixRows0.key o) =
    PureSixOrbitLookup0.representativeKey (PureSixOrbitLookup0.representativeOfCode c) at hz
  unfold PureSixActions0.actionKey at hz
  rw [SixCaseCompatibility0.unkey_rawRows] at hz
  rw [PureSixActions0.action_apply_eq]
  calc
    _ = PureSixRowModel0.unkey (PureSixRowModel0.key (PureSixActions0.applyRows (PureSixOrbitLookup0.groupOfCode c) (SixCaseCompatibility0.rawRows o))) :=
      (PureSixRowModel0.unkey_key _).symm
    _ = _ := congrArg PureSixRowModel0.unkey hz

lemma classification (o : Orders) (h : LocalBounds b hb o) :
    ∃ r : SixRepresentativeCertificates0.Representatives, r ∈ SixRepresentativeCertificates0.good ∧
      ∃ Q, Partition (code (FlatCanonicalKernel.src b hb o) (FlatCanonicalKernel.dst b hb o))
        Finset.univ Q ∧ Q.card = 2 := by
  obtain ⟨c,hc⟩ := SixCaseCompatibility0.exists_code o h
  let g := PureSixOrbitLookup0.groupOfCode c
  let r := PureSixOrbitLookup0.representativeOfCode c
  let a := PureSixActions0.action g
  let q := SixCaseCompatibility0.rawRows o
  let M := a.embedding PureSixRowModel0.edge q
  have ha : a.apply q = PureSixRowModel0.unkey (SixRepresentativeCertificates0.representativeKey r) := action_rows_eq o hc
  have hraw : ∀ Q, Partition (code (PureSixRowModel0.src q) (PureSixRowModel0.dst q)) Finset.univ Q → Q.card ≤ 6 := by
    intro Q hQ
    rw [SixCaseCompatibility0.src_rawRows o h,SixCaseCompatibility0.dst_rawRows o h] at hQ
    exact LocalBounds.flat_upper b hb o h Q hQ
  have hiff := M.upper_bound_map_iff Finset.univ 6
  have hmap : (Finset.univ : Finset PureSixRowModel0.E).map M.edge = Finset.univ := a.map_univ PureSixRowModel0.edge q
  rw [hmap] at hiff
  have hout := hiff.mpr hraw
  change ∀ Q, Partition (code (PureSixRowModel0.src (a.apply q)) (PureSixRowModel0.dst (a.apply q)))
    Finset.univ Q → Q.card ≤ 6 at hout
  rw [ha] at hout
  obtain ⟨hr,Q,hQ,hcQ⟩ := SixRepresentativeCertificates0.exists_two_of_upper r hout
  have hQ' : Partition (code (PureSixRowModel0.src (a.apply q)) (PureSixRowModel0.dst (a.apply q)))
      ((Finset.univ : Finset PureSixRowModel0.E).map M.edge) Q := by
    rw [hmap,ha]
    exact hQ
  obtain ⟨S,hS,hcS⟩ := unmap_partition_exists M.edge M.valid_map hQ'
  change Partition (code (PureSixRowModel0.src q) (PureSixRowModel0.dst q)) Finset.univ S at hS
  rw [SixCaseCompatibility0.src_rawRows o h,SixCaseCompatibility0.dst_rawRows o h] at hS
  exact ⟨r,hr,S,hS,hcS.trans hcQ⟩

lemma good_of_code (o : Orders) (h : LocalBounds b hb o) {c : ℕ}
    (hc : PureSixOrbitLookup0.table.lookup (SixRows0.key o) = some c) :
    PureSixOrbitLookup0.representativeOfCode c ∈ PureSixGoodLookup.representatives := by
  let g := PureSixOrbitLookup0.groupOfCode c
  let r := PureSixOrbitLookup0.representativeOfCode c
  let a := PureSixActions0.action g
  let q := SixCaseCompatibility0.rawRows o
  let M := a.embedding PureSixRowModel0.edge q
  have ha : a.apply q = PureSixRowModel0.unkey (SixRepresentativeCertificates0.representativeKey r) := action_rows_eq o hc
  have hraw : ∀ Q, Partition (code (PureSixRowModel0.src q) (PureSixRowModel0.dst q)) Finset.univ Q → Q.card ≤ 6 := by
    intro Q hQ
    rw [SixCaseCompatibility0.src_rawRows o h,SixCaseCompatibility0.dst_rawRows o h] at hQ
    exact LocalBounds.flat_upper b hb o h Q hQ
  have hiff := M.upper_bound_map_iff Finset.univ 6
  have hmap : (Finset.univ : Finset PureSixRowModel0.E).map M.edge = Finset.univ := a.map_univ PureSixRowModel0.edge q
  rw [hmap] at hiff
  have hout := hiff.mpr hraw
  change ∀ Q, Partition (code (PureSixRowModel0.src (a.apply q)) (PureSixRowModel0.dst (a.apply q)))
    Finset.univ Q → Q.card ≤ 6 at hout
  rw [ha] at hout
  obtain ⟨hr,_⟩ := SixRepresentativeCertificates0.exists_two_of_upper r hout
  simpa only [SixRepresentativeCertificates0.good,PureSixGoodLookup.representatives] using hr

lemma catalogue (o : Orders) (h : LocalBounds b hb o) :
    PureSixGoodLookup.Good (SixRows0.key o) := by
  obtain ⟨c,hc⟩ := SixCaseCompatibility0.exists_code o h
  exact PureSixOrbitLookup0.lookup_good hc (good_of_code o h hc)

#print axioms good_of_code
#print axioms catalogue

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
#print axioms classification
#print axioms exists_two
end Erdos184Work.SixOrbitKernel0
