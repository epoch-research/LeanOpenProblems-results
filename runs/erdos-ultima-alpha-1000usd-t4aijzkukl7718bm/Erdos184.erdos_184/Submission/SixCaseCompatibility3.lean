import Submission.SixRawBridge3
import Submission.SixProjectionCode30
import Submission.SixProjectionCode31
import Submission.SixProjectionCode32
import Submission.SixProjectionCode33
import Submission.SixProjectionCode34
import Submission.SixProjectionCode35
import Submission.PureSixComplete3

/-! Connecting actual canonical rows to the pure projected-word coverage check. -/
namespace Erdos184Work.SixCaseCompatibility3
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows3
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma compatible_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 60) (q5 : Fin 60)
    (h0 : SixProjectionCode30.Compatible q0 q1 q2 q3 q4 q5)
    (h1 : SixProjectionCode31.Compatible q0 q1 q2 q3 q4 q5)
    (h2 : SixProjectionCode32.Compatible q0 q1 q2 q3 q4 q5)
    (h3 : SixProjectionCode33.Compatible q0 q1 q2 q3 q4 q5)
    (h4 : SixProjectionCode34.Compatible q0 q1 q2 q3 q4 q5)
    (h5 : SixProjectionCode35.Compatible q0 q1 q2 q3 q4 q5)
    : PureSixLocalFilter3.Compatible q0 q1 q2 q3 q4 q5 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact PureSixLocalFilter3.forward0 (PureSixLocalFilter3.enc0_0 q2,PureSixLocalFilter3.enc0_1 q3,PureSixLocalFilter3.enc0_2 q4,PureSixLocalFilter3.enc0_3 q5,PureSixLocalFilter3.enc0_4 q1) h0
  · exact PureSixLocalFilter3.forward1 (PureSixLocalFilter3.enc1_0 q2,PureSixLocalFilter3.enc1_1 q3,PureSixLocalFilter3.enc1_2 q4,PureSixLocalFilter3.enc1_3 q5,PureSixLocalFilter3.enc1_4 q0) h1
  · exact PureSixLocalFilter3.forward2 (PureSixLocalFilter3.enc2_0 q0,PureSixLocalFilter3.enc2_1 q1,PureSixLocalFilter3.enc2_2 q4,PureSixLocalFilter3.enc2_3 q5,PureSixLocalFilter3.enc2_4 q3) h2
  · exact PureSixLocalFilter3.forward3 (PureSixLocalFilter3.enc3_0 q0,PureSixLocalFilter3.enc3_1 q1,PureSixLocalFilter3.enc3_2 q4,PureSixLocalFilter3.enc3_3 q5,PureSixLocalFilter3.enc3_4 q2) h3
  · exact PureSixLocalFilter3.forward4 (PureSixLocalFilter3.enc4_0 q0,PureSixLocalFilter3.enc4_1 q1,PureSixLocalFilter3.enc4_2 q2,PureSixLocalFilter3.enc4_3 q3,PureSixLocalFilter3.enc4_4 q5) h4
  · exact PureSixLocalFilter3.forward5 (PureSixLocalFilter3.enc5_0 q0,PureSixLocalFilter3.enc5_1 q1,PureSixLocalFilter3.enc5_2 q2,PureSixLocalFilter3.enc5_3 q3,PureSixLocalFilter3.enc5_4 q4) h5

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    PureSixLocalFilter3.Compatible (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5)) :=
  compatible_rows (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5))
    (SixProjectionCode30.compatible o h)    (SixProjectionCode31.compatible o h)    (SixProjectionCode32.compatible o h)    (SixProjectionCode33.compatible o h)    (SixProjectionCode34.compatible o h)    (SixProjectionCode35.compatible o h)

lemma lookup (o : Orders) (h : LocalBounds b hb o) :
    (PureSixLocalFilter3.output.lookup (SixRows3.key o)).isSome = true := by
  have hh := PureSixLocalFilter3.complete_rows (SixRows3.key0 (o 0)) (SixRows3.key1 (o 1)) (SixRows3.key2 (o 2)) (SixRows3.key3 (o 3)) (SixRows3.key4 (o 4)) (SixRows3.key5 (o 5)) (compatible o h)
  change (PureSixLocalFilter3.output.lookup (PureSixRowModel3.key (rawRows o))).isSome = true at hh
  rwa [key_rawRows] at hh
lemma not_localBounds (o : Orders) : ¬ LocalBounds b hb o := by
  intro h
  have hh := lookup o h
  simpa only [PureSixLocalFilter3.output,FiniteCaseLookup.Table.lookup,Option.isSome_none,Bool.false_eq_true] using hh
#print axioms not_localBounds
#print axioms src_rawRows
end Erdos184Work.SixCaseCompatibility3
