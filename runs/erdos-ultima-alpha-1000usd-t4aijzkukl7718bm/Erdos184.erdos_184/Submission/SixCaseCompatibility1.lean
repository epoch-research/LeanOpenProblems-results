import Submission.SixRawBridge1
import Submission.SixProjectionCode10
import Submission.SixProjectionCode11
import Submission.SixProjectionCode12
import Submission.SixProjectionCode13
import Submission.SixProjectionCode14
import Submission.SixProjectionCode15
import Submission.PureSixComplete1

/-! Connecting actual canonical rows to the pure projected-word coverage check. -/
namespace Erdos184Work.SixCaseCompatibility1
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows1
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma compatible_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12)
    (h0 : SixProjectionCode10.Compatible q0 q1 q2 q3 q4 q5)
    (h1 : SixProjectionCode11.Compatible q0 q1 q2 q3 q4 q5)
    (h2 : SixProjectionCode12.Compatible q0 q1 q2 q3 q4 q5)
    (h3 : SixProjectionCode13.Compatible q0 q1 q2 q3 q4 q5)
    (h4 : SixProjectionCode14.Compatible q0 q1 q2 q3 q4 q5)
    (h5 : SixProjectionCode15.Compatible q0 q1 q2 q3 q4 q5)
    : PureSixLocalFilter1.Compatible q0 q1 q2 q3 q4 q5 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact PureSixLocalFilter1.forward0 (PureSixLocalFilter1.enc0_0 q1,PureSixLocalFilter1.enc0_1 q2,PureSixLocalFilter1.enc0_2 q3,PureSixLocalFilter1.enc0_3 q4,PureSixLocalFilter1.enc0_4 q5) h0
  · exact PureSixLocalFilter1.forward1 (PureSixLocalFilter1.enc1_0 q0,PureSixLocalFilter1.enc1_1 q2,PureSixLocalFilter1.enc1_2 q3,PureSixLocalFilter1.enc1_3 q4,PureSixLocalFilter1.enc1_4 q5) h1
  · exact PureSixLocalFilter1.forward2 (PureSixLocalFilter1.enc2_0 q0,PureSixLocalFilter1.enc2_1 q1,PureSixLocalFilter1.enc2_2 q3,PureSixLocalFilter1.enc2_3 q4,PureSixLocalFilter1.enc2_4 q5) h2
  · exact PureSixLocalFilter1.forward3 (PureSixLocalFilter1.enc3_0 q0,PureSixLocalFilter1.enc3_1 q1,PureSixLocalFilter1.enc3_2 q2,PureSixLocalFilter1.enc3_3 q4,PureSixLocalFilter1.enc3_4 q5) h3
  · exact PureSixLocalFilter1.forward4 (PureSixLocalFilter1.enc4_0 q0,PureSixLocalFilter1.enc4_1 q1,PureSixLocalFilter1.enc4_2 q2,PureSixLocalFilter1.enc4_3 q3,PureSixLocalFilter1.enc4_4 q5) h4
  · exact PureSixLocalFilter1.forward5 (PureSixLocalFilter1.enc5_0 q0,PureSixLocalFilter1.enc5_1 q1,PureSixLocalFilter1.enc5_2 q2,PureSixLocalFilter1.enc5_3 q3,PureSixLocalFilter1.enc5_4 q4) h5

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    PureSixLocalFilter1.Compatible (SixRows1.key0 (o 0)) (SixRows1.key1 (o 1)) (SixRows1.key2 (o 2)) (SixRows1.key3 (o 3)) (SixRows1.key4 (o 4)) (SixRows1.key5 (o 5)) :=
  compatible_rows (SixRows1.key0 (o 0)) (SixRows1.key1 (o 1)) (SixRows1.key2 (o 2)) (SixRows1.key3 (o 3)) (SixRows1.key4 (o 4)) (SixRows1.key5 (o 5))
    (SixProjectionCode10.compatible o h)    (SixProjectionCode11.compatible o h)    (SixProjectionCode12.compatible o h)    (SixProjectionCode13.compatible o h)    (SixProjectionCode14.compatible o h)    (SixProjectionCode15.compatible o h)

lemma lookup (o : Orders) (h : LocalBounds b hb o) :
    (PureSixLocalFilter1.output.lookup (SixRows1.key o)).isSome = true := by
  have hh := PureSixLocalFilter1.complete_rows (SixRows1.key0 (o 0)) (SixRows1.key1 (o 1)) (SixRows1.key2 (o 2)) (SixRows1.key3 (o 3)) (SixRows1.key4 (o 4)) (SixRows1.key5 (o 5)) (compatible o h)
  change (PureSixLocalFilter1.output.lookup (PureSixRowModel1.key (rawRows o))).isSome = true at hh
  rwa [key_rawRows] at hh
lemma exists_code (o : Orders) (h : LocalBounds b hb o) :
    ∃ c, PureSixOrbitLookup1.table.lookup (SixRows1.key o) = some c := by
  exact Option.isSome_iff_exists.mp (lookup o h)
#print axioms exists_code
#print axioms src_rawRows
end Erdos184Work.SixCaseCompatibility1
