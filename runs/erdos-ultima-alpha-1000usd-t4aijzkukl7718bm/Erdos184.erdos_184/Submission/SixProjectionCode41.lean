import Submission.FiniteIntervals
import Submission.SixProjectionCode41RowsBase
import Submission.SixProjectionCode41Row0
import Submission.SixProjectionCode41Row1
import Submission.SixProjection41
import Submission.SixRows4
import Submission.FiveWordOrbits1

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.SixProjectionCode41
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection41
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false



lemma row2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex =
      FiveRows1.words2 (FiveRows1.key2 (smallOrder2 q)) →
    enc2 (SixRows4.key3 q) = (FiveRows1.key2 (smallOrder2 q)).val + 1 := by decide +kernel

lemma row3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex =
      FiveRows1.words3 (FiveRows1.key3 (smallOrder3 q)) →
    enc3 (SixRows4.key4 q) = (FiveRows1.key3 (smallOrder3 q)).val + 1 := by decide +kernel

lemma row4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex =
      FiveRows1.words4 (FiveRows1.key4 (smallOrder4 q)) →
    enc4 (SixRows4.key5 q) = (FiveRows1.key4 (smallOrder4 q)).val + 1 := by decide +kernel

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(1,8,1,1,3),(1,8,3,1,2),(1,8,3,1,3),(1,9,1,2,3),(1,9,3,2,2),(1,9,3,2,3),(1,10,1,1,2),(1,10,1,1,3),(1,10,1,2,2),(1,10,1,2,3),(1,10,1,3,2),(1,10,1,3,3),(1,10,3,1,2),(1,10,3,2,2),(1,10,3,3,2),(2,7,2,3,1),(2,7,3,2,1),(2,7,3,3,1),(2,9,2,2,1),(2,9,2,2,2),(2,9,2,2,3),(2,9,2,3,1),(2,9,2,3,2),(2,9,2,3,3),(2,9,3,2,1),(2,9,3,2,2),(2,9,3,2,3),(2,10,2,3,2),(2,10,3,2,2),(2,10,3,3,2),(3,8,1,1,1),(3,8,1,1,3),(3,8,1,3,1),(3,8,2,1,1),(3,8,2,1,3),(3,8,2,3,1),(3,8,3,1,1),(3,8,3,1,3),(3,8,3,3,1),(3,10,1,1,3),(3,10,1,3,1),(3,10,1,3,3),(3,12,2,1,3),(3,12,2,3,1),(3,12,2,3,3),(4,8,2,3,1),(4,8,3,2,1),(4,8,3,3,1),(4,11,2,3,2),(4,11,3,2,2),(4,11,3,3,2),(4,12,2,2,1),(4,12,2,2,2),(4,12,2,2,3),(4,12,2,3,1),(4,12,2,3,2),(4,12,2,3,3),(4,12,3,2,1),(4,12,3,2,2),(4,12,3,2,3),(5,7,1,1,1),(5,7,1,1,3),(5,7,1,3,1),(5,7,2,1,1),(5,7,2,1,3),(5,7,2,3,1),(5,7,3,1,1),(5,7,3,1,3),(5,7,3,3,1),(5,9,2,1,3),(5,9,2,3,1),(5,9,2,3,3),(5,11,1,1,3),(5,11,1,3,1),(5,11,1,3,3),(6,7,1,1,3),(6,7,3,1,2),(6,7,3,1,3),(6,11,1,1,2),(6,11,1,1,3),(6,11,1,2,2),(6,11,1,2,3),(6,11,1,3,2),(6,11,1,3,3),(6,11,3,1,2),(6,11,3,2,2),(6,11,3,3,2),(6,12,1,2,3),(6,12,3,2,2),(6,12,3,2,3),(7,2,1,3,2),(7,2,3,1,2),(7,2,3,3,2),(7,5,1,2,2),(7,5,1,2,3),(7,5,1,3,2),(7,5,2,2,2),(7,5,2,2,3),(7,5,2,3,2),(7,5,3,2,2),(7,5,3,2,3),(7,5,3,3,2),(7,6,2,2,3),(7,6,3,2,1),(7,6,3,2,3),(7,8,3,1,1),(7,8,3,1,2),(7,8,3,1,3),(7,8,3,2,1),(7,8,3,2,2),(7,8,3,2,3),(7,8,3,3,1),(7,8,3,3,2),(7,9,2,2,3),(7,9,3,2,2),(7,9,3,2,3),(7,10,1,2,2),(7,10,1,3,1),(7,10,1,3,2),(7,10,1,3,3),(7,10,2,3,2),(7,10,3,1,2),(7,10,3,2,1),(7,10,3,2,2),(7,10,3,2,3),(7,10,3,3,1),(7,10,3,3,2),(7,11,1,3,2),(7,11,3,2,2),(7,11,3,3,2),(7,12,1,2,3),(7,12,2,1,3),(7,12,2,2,2),(7,12,2,2,3),(7,12,2,3,3),(7,12,3,1,2),(7,12,3,1,3),(7,12,3,2,1),(7,12,3,2,2),(7,12,3,2,3),(7,12,3,3,2),(8,1,2,2,3),(8,1,3,2,1),(8,1,3,2,3),(8,3,1,2,2),(8,3,1,2,3),(8,3,1,3,2),(8,3,2,2,2),(8,3,2,2,3),(8,3,2,3,2),(8,3,3,2,2),(8,3,3,2,3),(8,3,3,3,2),(8,4,1,3,2),(8,4,3,1,2),(8,4,3,3,2),(8,7,3,1,1),(8,7,3,1,2),(8,7,3,1,3),(8,7,3,2,1),(8,7,3,2,2),(8,7,3,2,3),(8,7,3,3,1),(8,7,3,3,2),(8,9,1,2,3),(8,9,2,1,3),(8,9,2,2,2),(8,9,2,2,3),(8,9,2,3,3),(8,9,3,1,2),(8,9,3,1,3),(8,9,3,2,1),(8,9,3,2,2),(8,9,3,2,3),(8,9,3,3,2),(8,10,1,3,2),(8,10,3,2,2),(8,10,3,3,2),(8,11,1,2,2),(8,11,1,3,1),(8,11,1,3,2),(8,11,1,3,3),(8,11,2,3,2),(8,11,3,1,2),(8,11,3,2,1),(8,11,3,2,2),(8,11,3,2,3),(8,11,3,3,1),(8,11,3,3,2),(8,12,2,2,3),(8,12,3,2,2),(8,12,3,2,3),(9,1,2,1,3),(9,1,3,1,1),(9,1,3,1,3),(9,2,1,1,1),(9,2,1,1,2),(9,2,1,1,3),(9,2,1,3,1),(9,2,1,3,2),(9,2,1,3,3),(9,2,3,1,1),(9,2,3,1,2),(9,2,3,1,3),(9,5,1,2,3),(9,5,1,3,2),(9,5,1,3,3),(9,7,1,1,3),(9,7,3,1,1),(9,7,3,1,3),(9,8,1,1,1),(9,8,1,1,3),(9,8,1,2,3),(9,8,1,3,3),(9,8,2,1,3),(9,8,3,1,1),(9,8,3,1,2),(9,8,3,1,3),(9,8,3,2,1),(9,8,3,2,3),(9,8,3,3,1),(9,10,1,1,3),(9,10,1,3,2),(9,10,1,3,3),(9,11,1,1,2),(9,11,1,1,3),(9,11,1,2,3),(9,11,1,3,1),(9,11,1,3,2),(9,11,1,3,3),(9,11,2,1,3),(9,11,2,3,2),(9,11,2,3,3),(9,11,3,1,3),(9,11,3,3,2),(9,12,1,1,3),(9,12,1,2,3),(9,12,1,3,3),(9,12,2,1,3),(9,12,2,2,3),(9,12,2,3,3),(9,12,3,1,3),(9,12,3,2,3),(10,1,2,1,1),(10,1,2,1,3),(10,1,2,2,1),(10,1,2,2,3),(10,1,2,3,1),(10,1,2,3,3),(10,1,3,1,1),(10,1,3,2,1),(10,1,3,3,1),(10,2,1,3,1),(10,2,3,1,1),(10,2,3,3,1),(10,3,2,2,3),(10,3,2,3,2),(10,3,2,3,3),(10,7,1,3,1),(10,7,2,1,1),(10,7,2,3,1),(10,7,2,3,2),(10,7,2,3,3),(10,7,3,1,1),(10,7,3,1,2),(10,7,3,1,3),(10,7,3,2,1),(10,7,3,3,1),(10,7,3,3,2),(10,8,2,3,1),(10,8,3,1,1),(10,8,3,3,1),(10,9,2,2,3),(10,9,2,3,1),(10,9,2,3,3),(10,11,1,3,1),(10,11,1,3,2),(10,11,1,3,3),(10,11,2,3,1),(10,11,2,3,2),(10,11,2,3,3),(10,11,3,3,1),(10,11,3,3,2),(10,12,1,2,3),(10,12,1,3,1),(10,12,1,3,3),(10,12,2,1,3),(10,12,2,2,1),(10,12,2,2,3),(10,12,2,3,1),(10,12,2,3,2),(10,12,2,3,3),(10,12,3,2,3),(10,12,3,3,1),(11,4,1,3,1),(11,4,3,1,1),(11,4,3,3,1),(11,5,2,2,3),(11,5,2,3,2),(11,5,2,3,3),(11,6,2,1,1),(11,6,2,1,3),(11,6,2,2,1),(11,6,2,2,3),(11,6,2,3,1),(11,6,2,3,3),(11,6,3,1,1),(11,6,3,2,1),(11,6,3,3,1),(11,7,2,3,1),(11,7,3,1,1),(11,7,3,3,1),(11,8,1,3,1),(11,8,2,1,1),(11,8,2,3,1),(11,8,2,3,2),(11,8,2,3,3),(11,8,3,1,1),(11,8,3,1,2),(11,8,3,1,3),(11,8,3,2,1),(11,8,3,3,1),(11,8,3,3,2),(11,9,1,2,3),(11,9,1,3,1),(11,9,1,3,3),(11,9,2,1,3),(11,9,2,2,1),(11,9,2,2,3),(11,9,2,3,1),(11,9,2,3,2),(11,9,2,3,3),(11,9,3,2,3),(11,9,3,3,1),(11,10,1,3,1),(11,10,1,3,2),(11,10,1,3,3),(11,10,2,3,1),(11,10,2,3,2),(11,10,2,3,3),(11,10,3,3,1),(11,10,3,3,2),(11,12,2,2,3),(11,12,2,3,1),(11,12,2,3,3),(12,3,1,2,3),(12,3,1,3,2),(12,3,1,3,3),(12,4,1,1,1),(12,4,1,1,2),(12,4,1,1,3),(12,4,1,3,1),(12,4,1,3,2),(12,4,1,3,3),(12,4,3,1,1),(12,4,3,1,2),(12,4,3,1,3),(12,6,2,1,3),(12,6,3,1,1),(12,6,3,1,3),(12,7,1,1,1),(12,7,1,1,3),(12,7,1,2,3),(12,7,1,3,3),(12,7,2,1,3),(12,7,3,1,1),(12,7,3,1,2),(12,7,3,1,3),(12,7,3,2,1),(12,7,3,2,3),(12,7,3,3,1),(12,8,1,1,3),(12,8,3,1,1),(12,8,3,1,3),(12,9,1,1,3),(12,9,1,2,3),(12,9,1,3,3),(12,9,2,1,3),(12,9,2,2,3),(12,9,2,3,3),(12,9,3,1,3),(12,9,3,2,3),(12,10,1,1,2),(12,10,1,1,3),(12,10,1,2,3),(12,10,1,3,1),(12,10,1,3,2),(12,10,1,3,3),(12,10,2,1,3),(12,10,2,3,2),(12,10,2,3,3),(12,10,3,1,3),(12,10,3,3,2),(12,11,1,1,3),(12,11,1,3,2),(12,11,1,3,3)}
def Compatible (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Prop :=
  (enc0 q0,enc1 q2,enc2 q3,enc3 q4,enc4 q5) ∈ goodCodes
instance (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Decidable (Compatible q0 q1 q2 q3 q4 q5) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

/- Direct catalogue insertion proofs avoid evaluating nested finset deduplication. -/
def CodesIndex (j : ℕ) : Prop := ∀ hj : j < 396,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨j,hj⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨j,hj⟩).val).val + 1) ∈ goodCodes
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk00"
lemma codes_chunk00 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨0+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨0+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (1,8,1,1,3) ∈ goodCodes
    unfold goodCodes
    exact Finset.mem_insert_self _ _
  · change (1,8,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,8,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,9,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,9,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,9,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,1,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,1,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (1,10,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,7,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval00 : FiniteIntervals.Covers CodesIndex 0 16 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 0 16
  intro i hj
  exact codes_chunk00 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk01"
lemma codes_chunk01 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨16+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨16+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (2,7,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 16 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,7,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 17 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,2,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 18 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,2,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 19 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 20 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 21 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 22 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 23 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 24 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 25 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,9,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 26 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,10,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 27 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,10,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 28 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (2,10,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 29 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,1,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 30 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 31 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval01 : FiniteIntervals.Covers CodesIndex 16 32 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 16 16
  intro i hj
  exact codes_chunk01 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk02"
lemma codes_chunk02 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨32+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨32+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (3,8,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 32 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,2,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 33 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 34 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 35 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 36 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 37 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,8,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 38 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,10,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 39 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,10,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 40 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,10,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 41 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,12,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 42 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,12,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 43 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (3,12,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 44 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,8,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 45 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,8,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 46 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,8,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 47 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval02 : FiniteIntervals.Covers CodesIndex 32 48 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 32 16
  intro i hj
  exact codes_chunk02 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk03"
lemma codes_chunk03 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨48+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨48+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (4,11,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 48 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,11,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 49 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,11,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 50 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,2,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 51 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,2,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 52 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 53 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 54 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 55 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 56 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 57 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 58 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (4,12,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 59 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,1,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 60 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 61 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 62 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,2,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 63 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval03 : FiniteIntervals.Covers CodesIndex 48 64 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 48 16
  intro i hj
  exact codes_chunk03 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk04"
lemma codes_chunk04 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨64+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨64+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (5,7,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 64 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 65 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 66 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 67 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,7,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 68 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,9,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 69 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,9,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 70 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,9,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 71 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,11,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 72 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,11,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 73 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (5,11,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 74 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,7,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 75 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,7,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 76 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,7,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 77 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,1,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 78 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 79 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval04 : FiniteIntervals.Covers CodesIndex 64 80 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 64 16
  intro i hj
  exact codes_chunk04 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk05"
lemma codes_chunk05 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨80+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨80+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (6,11,1,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 80 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 81 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 82 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 83 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 84 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 85 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,11,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 86 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,12,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 87 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,12,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 88 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (6,12,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 89 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,2,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 90 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,2,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 91 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,2,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 92 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,1,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 93 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 94 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 95 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval05 : FiniteIntervals.Covers CodesIndex 80 96 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 80 16
  intro i hj
  exact codes_chunk05 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk06"
lemma codes_chunk06 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨96+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨96+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (7,5,2,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 96 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 97 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 98 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 99 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 100 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,5,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 101 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,6,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 102 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,6,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 103 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,6,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 104 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,8,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 105 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,8,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 106 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,8,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 107 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,8,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 108 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,8,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 109 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,8,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 110 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,8,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 111 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval06 : FiniteIntervals.Covers CodesIndex 96 112 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 96 16
  intro i hj
  exact codes_chunk06 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk07"
lemma codes_chunk07 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨112+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨112+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (7,8,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 112 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,9,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 113 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,9,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 114 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,9,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 115 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,1,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 116 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 117 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 118 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 119 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 120 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 121 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 122 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 123 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 124 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 125 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,10,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 126 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,11,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 127 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval07 : FiniteIntervals.Covers CodesIndex 112 128 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 112 16
  intro i hj
  exact codes_chunk07 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk08"
lemma codes_chunk08 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨128+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨128+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (7,11,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 128 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,11,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 129 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 130 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 131 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,2,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 132 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 133 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 134 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 135 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 136 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 137 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 138 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 139 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (7,12,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 140 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,1,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 141 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,1,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 142 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,1,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 143 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval08 : FiniteIntervals.Covers CodesIndex 128 144 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 128 16
  intro i hj
  exact codes_chunk08 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk09"
lemma codes_chunk09 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨144+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨144+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (8,3,1,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 144 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 145 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 146 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,2,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 147 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 148 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 149 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 150 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 151 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,3,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 152 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,4,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 153 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,4,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 154 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,4,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 155 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,7,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 156 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,7,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 157 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,7,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 158 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,7,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 159 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval09 : FiniteIntervals.Covers CodesIndex 144 160 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 144 16
  intro i hj
  exact codes_chunk09 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk10"
lemma codes_chunk10 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨160+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨160+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨160+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨160+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨160+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (8,7,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 160 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,7,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 161 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,7,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 162 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,7,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 163 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 164 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 165 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,2,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 166 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 167 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 168 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 169 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 170 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 171 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 172 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 173 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,9,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 174 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,10,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 175 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval10 : FiniteIntervals.Covers CodesIndex 160 176 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 160 16
  intro i hj
  exact codes_chunk10 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk11"
lemma codes_chunk11 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨176+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨176+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨176+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨176+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨176+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (8,10,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 176 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,10,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 177 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,1,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 178 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 179 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 180 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 181 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 182 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 183 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 184 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 185 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 186 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 187 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,11,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 188 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,12,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 189 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,12,3,2,2) ∈ goodCodes
    unfold goodCodes
    iterate 190 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (8,12,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 191 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval11 : FiniteIntervals.Covers CodesIndex 176 192 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 176 16
  intro i hj
  exact codes_chunk11 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk12"
lemma codes_chunk12 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨192+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨192+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨192+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨192+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨192+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (9,1,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 192 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,1,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 193 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,1,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 194 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,1,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 195 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,1,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 196 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 197 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 198 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 199 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 200 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 201 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 202 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,2,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 203 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,5,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 204 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,5,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 205 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,5,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 206 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,7,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 207 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval12 : FiniteIntervals.Covers CodesIndex 192 208 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 192 16
  intro i hj
  exact codes_chunk12 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk13"
lemma codes_chunk13 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨208+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨208+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨208+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨208+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨208+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (9,7,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 208 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,7,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 209 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,1,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 210 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 211 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 212 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 213 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 214 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 215 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 216 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 217 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 218 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 219 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,8,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 220 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,10,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 221 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,10,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 222 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,10,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 223 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval13 : FiniteIntervals.Covers CodesIndex 208 224 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 208 16
  intro i hj
  exact codes_chunk13 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk14"
lemma codes_chunk14 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨224+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨224+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨224+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨224+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨224+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (9,11,1,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 224 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 225 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 226 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 227 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 228 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 229 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 230 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 231 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 232 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 233 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,11,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 234 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,12,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 235 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,12,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 236 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,12,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 237 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,12,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 238 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,12,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 239 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval14 : FiniteIntervals.Covers CodesIndex 224 240 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 224 16
  intro i hj
  exact codes_chunk14 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk15"
lemma codes_chunk15 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨240+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨240+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨240+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨240+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨240+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (9,12,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 240 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,12,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 241 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (9,12,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 242 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,2,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 243 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 244 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,2,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 245 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 246 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 247 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 248 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 249 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 250 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,1,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 251 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,2,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 252 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,2,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 253 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,2,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 254 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,3,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 255 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval15 : FiniteIntervals.Covers CodesIndex 240 256 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 240 16
  intro i hj
  exact codes_chunk15 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk16"
lemma codes_chunk16 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨256+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨256+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨256+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨256+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨256+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (10,3,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 256 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,3,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 257 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 258 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,2,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 259 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 260 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 261 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 262 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 263 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 264 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 265 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 266 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 267 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,7,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 268 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,8,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 269 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,8,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 270 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,8,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 271 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval16 : FiniteIntervals.Covers CodesIndex 256 272 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 256 16
  intro i hj
  exact codes_chunk16 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk17"
lemma codes_chunk17 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨272+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨272+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨272+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨272+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨272+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (10,9,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 272 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,9,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 273 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,9,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 274 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 275 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 276 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 277 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 278 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 279 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 280 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 281 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,11,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 282 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 283 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 284 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 285 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 286 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,2,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 287 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval17 : FiniteIntervals.Covers CodesIndex 272 288 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 272 16
  intro i hj
  exact codes_chunk17 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk18"
lemma codes_chunk18 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨288+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨288+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨288+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨288+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨288+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (10,12,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 288 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 289 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 290 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 291 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 292 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (10,12,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 293 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,4,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 294 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,4,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 295 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,4,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 296 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,5,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 297 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,5,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 298 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,5,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 299 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,2,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 300 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 301 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,2,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 302 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 303 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval18 : FiniteIntervals.Covers CodesIndex 288 304 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 288 16
  intro i hj
  exact codes_chunk18 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk19"
lemma codes_chunk19 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨304+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨304+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨304+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨304+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨304+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (11,6,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 304 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 305 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 306 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 307 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,6,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 308 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,7,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 309 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,7,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 310 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,7,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 311 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 312 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,2,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 313 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 314 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 315 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 316 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 317 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 318 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 319 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval19 : FiniteIntervals.Covers CodesIndex 304 320 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 304 16
  intro i hj
  exact codes_chunk19 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk20"
lemma codes_chunk20 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨320+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨320+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨320+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨320+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨320+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (11,8,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 320 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 321 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,8,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 322 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 323 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 324 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 325 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 326 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,2,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 327 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 328 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 329 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 330 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 331 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 332 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,9,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 333 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,10,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 334 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,10,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 335 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval20 : FiniteIntervals.Covers CodesIndex 320 336 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 320 16
  intro i hj
  exact codes_chunk20 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk21"
lemma codes_chunk21 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨336+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨336+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨336+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨336+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨336+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (11,10,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 336 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,10,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 337 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,10,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 338 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,10,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 339 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,10,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 340 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,10,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 341 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,12,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 342 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,12,2,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 343 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (11,12,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 344 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,3,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 345 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,3,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 346 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,3,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 347 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,1,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 348 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,1,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 349 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 350 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 351 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval21 : FiniteIntervals.Covers CodesIndex 336 352 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 336 16
  intro i hj
  exact codes_chunk21 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk22"
lemma codes_chunk22 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨352+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨352+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨352+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨352+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨352+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (12,4,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 352 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 353 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 354 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 355 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,4,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 356 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,6,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 357 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,6,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 358 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,6,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 359 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,1,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 360 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 361 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 362 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 363 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 364 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 365 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,3,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 366 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 367 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval22 : FiniteIntervals.Covers CodesIndex 352 368 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 352 16
  intro i hj
  exact codes_chunk22 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk23"
lemma codes_chunk23 : ∀ i : Fin 16,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨368+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨368+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨368+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨368+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨368+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (12,7,3,2,1) ∈ goodCodes
    unfold goodCodes
    iterate 368 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 369 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,7,3,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 370 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,8,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 371 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,8,3,1,1) ∈ goodCodes
    unfold goodCodes
    iterate 372 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,8,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 373 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 374 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 375 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 376 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 377 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,2,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 378 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 379 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 380 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,9,3,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 381 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,1,1,2) ∈ goodCodes
    unfold goodCodes
    iterate 382 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 383 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
lemma codes_interval23 : FiniteIntervals.Covers CodesIndex 368 384 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 368 16
  intro i hj
  exact codes_chunk23 i
#eval IO.FS.writeFile "/tmp/code41-current-command" "begin codes_chunk24"
lemma codes_chunk24 : ∀ i : Fin 12,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey ⟨384+i.val,by omega⟩).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey ⟨384+i.val,by omega⟩).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey ⟨384+i.val,by omega⟩).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey ⟨384+i.val,by omega⟩).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey ⟨384+i.val,by omega⟩).val).val + 1) ∈ goodCodes := by
  intro i
  fin_cases i
  · change (12,10,1,2,3) ∈ goodCodes
    unfold goodCodes
    iterate 384 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,1,3,1) ∈ goodCodes
    unfold goodCodes
    iterate 385 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 386 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 387 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,2,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 388 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,2,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 389 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,2,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 390 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,3,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 391 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,10,3,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 392 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,11,1,1,3) ∈ goodCodes
    unfold goodCodes
    iterate 393 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,11,1,3,2) ∈ goodCodes
    unfold goodCodes
    iterate 394 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  · change (12,11,1,3,3) ∈ goodCodes
    unfold goodCodes
    iterate 395 apply Finset.mem_insert_of_mem
    exact Finset.mem_singleton_self _
lemma codes_interval24 : FiniteIntervals.Covers CodesIndex 384 396 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 384 12
  intro i hj
  exact codes_chunk24 i
lemma codes_valid : ∀ i : FiveWordOrbits1.Cases,
    ((FiveRows1.digit0 (FiveWordOrbits1.caseKey i).val).val + 1,(FiveRows1.digit1 (FiveWordOrbits1.caseKey i).val).val + 1,(FiveRows1.digit2 (FiveWordOrbits1.caseKey i).val).val + 1,(FiveRows1.digit3 (FiveWordOrbits1.caseKey i).val).val + 1,(FiveRows1.digit4 (FiveWordOrbits1.caseKey i).val).val + 1) ∈ goodCodes := by
  intro i
  have hc : FiniteIntervals.Covers CodesIndex 0 396 := (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge codes_interval00 (FiniteIntervals.merge codes_interval01 codes_interval02)) (FiniteIntervals.merge codes_interval03 (FiniteIntervals.merge codes_interval04 codes_interval05))) (FiniteIntervals.merge (FiniteIntervals.merge codes_interval06 (FiniteIntervals.merge codes_interval07 codes_interval08)) (FiniteIntervals.merge codes_interval09 (FiniteIntervals.merge codes_interval10 codes_interval11)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge codes_interval12 (FiniteIntervals.merge codes_interval13 codes_interval14)) (FiniteIntervals.merge codes_interval15 (FiniteIntervals.merge codes_interval16 codes_interval17))) (FiniteIntervals.merge (FiniteIntervals.merge codes_interval18 (FiniteIntervals.merge codes_interval19 codes_interval20)) (FiniteIntervals.merge (FiniteIntervals.merge codes_interval21 codes_interval22) (FiniteIntervals.merge codes_interval23 codes_interval24)))))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma codes_of_good (j : Fin 3888) (hj : j ∈ FiveRows1.good) :
    ((FiveRows1.digit0 j.val).val + 1,(FiveRows1.digit1 j.val).val + 1,(FiveRows1.digit2 j.val).val + 1,(FiveRows1.digit3 j.val).val + 1,(FiveRows1.digit4 j.val).val + 1) ∈ goodCodes := by
  rw [FiveWordOrbits1.good_eq] at hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact codes_valid i

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5)) := by
  have hs := SixProjection41.localBounds o h
  have hc := codes_of_good ⟨FiveRows1.key (smallOrders o),FiveRows1.key_lt (smallOrders o)⟩
    (SixProjection41.catalogue o h)
  rw [FiveRows1.digit_key0,FiveRows1.digit_key1,FiveRows1.digit_key2,FiveRows1.digit_key3,FiveRows1.digit_key4] at hc
  have hr0 := FiveRows1.chosen0 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr0
  have he0 := row0 (o 0) hr0
  have hr1 := FiveRows1.chosen1 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr1
  have he1 := row1 (o 2) hr1
  have hr2 := FiveRows1.chosen2 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr2
  have he2 := row2 (o 3) hr2
  have hr3 := FiveRows1.chosen3 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr3
  have he3 := row3 (o 4) hr3
  have hr4 := FiveRows1.chosen4 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr4
  have he4 := row4 (o 5) hr4
  unfold Compatible
  rw [he0,he1,he2,he3,he4]
  simpa only [smallOrders,Fin.cases_zero,Fin.cases_succ] using hc

#print axioms compatible
end Erdos184Work.SixProjectionCode41
