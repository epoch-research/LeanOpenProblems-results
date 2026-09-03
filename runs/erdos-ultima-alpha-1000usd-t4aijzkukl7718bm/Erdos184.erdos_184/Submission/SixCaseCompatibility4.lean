import Submission.SixRawBridge4
import Submission.SixProjectionCode40
import Submission.SixProjectionCode41
import Submission.SixProjectionCode42
import Submission.SixProjectionCode43
import Submission.SixProjectionCode44
import Submission.SixProjectionCode45
import Submission.PureSixComplete4

/-! Connecting actual canonical rows to the pure projected-word coverage check. -/
namespace Erdos184Work.SixCaseCompatibility4
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows4
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma compatible_rows (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12)
    (h0 : SixProjectionCode40.Compatible q0 q1 q2 q3 q4 q5)
    (h1 : SixProjectionCode41.Compatible q0 q1 q2 q3 q4 q5)
    (h2 : SixProjectionCode42.Compatible q0 q1 q2 q3 q4 q5)
    (h3 : SixProjectionCode43.Compatible q0 q1 q2 q3 q4 q5)
    (h4 : SixProjectionCode44.Compatible q0 q1 q2 q3 q4 q5)
    (h5 : SixProjectionCode45.Compatible q0 q1 q2 q3 q4 q5)
    : PureSixLocalFilter4.Compatible q0 q1 q2 q3 q4 q5 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact PureSixLocalFilter4.forward0 (PureSixLocalFilter4.enc0_0 q1,PureSixLocalFilter4.enc0_1 q2,PureSixLocalFilter4.enc0_2 q3,PureSixLocalFilter4.enc0_3 q4,PureSixLocalFilter4.enc0_4 q5) h0
  · exact PureSixLocalFilter4.forward1 (PureSixLocalFilter4.enc1_0 q0,PureSixLocalFilter4.enc1_1 q2,PureSixLocalFilter4.enc1_2 q3,PureSixLocalFilter4.enc1_3 q4,PureSixLocalFilter4.enc1_4 q5) h1
  · exact PureSixLocalFilter4.forward2 (PureSixLocalFilter4.enc2_0 q0,PureSixLocalFilter4.enc2_1 q1,PureSixLocalFilter4.enc2_2 q3,PureSixLocalFilter4.enc2_3 q4,PureSixLocalFilter4.enc2_4 q5) h2
  · exact PureSixLocalFilter4.forward3 (PureSixLocalFilter4.enc3_0 q0,PureSixLocalFilter4.enc3_1 q1,PureSixLocalFilter4.enc3_2 q2,PureSixLocalFilter4.enc3_3 q4,PureSixLocalFilter4.enc3_4 q5) h3
  · exact PureSixLocalFilter4.forward4 (PureSixLocalFilter4.enc4_0 q0,PureSixLocalFilter4.enc4_1 q1,PureSixLocalFilter4.enc4_2 q2,PureSixLocalFilter4.enc4_3 q3,PureSixLocalFilter4.enc4_4 q5) h4
  · exact PureSixLocalFilter4.forward5 (PureSixLocalFilter4.enc5_0 q0,PureSixLocalFilter4.enc5_1 q1,PureSixLocalFilter4.enc5_2 q2,PureSixLocalFilter4.enc5_3 q3,PureSixLocalFilter4.enc5_4 q4) h5

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    PureSixLocalFilter4.Compatible (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5)) :=
  compatible_rows (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5))
    (SixProjectionCode40.compatible o h)    (SixProjectionCode41.compatible o h)    (SixProjectionCode42.compatible o h)    (SixProjectionCode43.compatible o h)    (SixProjectionCode44.compatible o h)    (SixProjectionCode45.compatible o h)

lemma lookup (o : Orders) (h : LocalBounds b hb o) :
    (PureSixLocalFilter4.output.lookup (SixRows4.key o)).isSome = true := by
  have hh := PureSixLocalFilter4.complete_rows (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5)) (compatible o h)
  change (PureSixLocalFilter4.output.lookup (PureSixRowModel4.key (rawRows o))).isSome = true at hh
  rwa [key_rawRows] at hh
lemma not_localBounds (o : Orders) : ¬ LocalBounds b hb o := by
  intro h
  have hh := lookup o h
  simpa only [PureSixLocalFilter4.output,FiniteCaseLookup.Table.lookup,Option.isSome_none,Bool.false_eq_true] using hh
#print axioms not_localBounds
#print axioms src_rawRows
end Erdos184Work.SixCaseCompatibility4
