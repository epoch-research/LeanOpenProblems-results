import Submission.SixRawBridge0
import Submission.SixProjectionCode00
import Submission.SixProjectionCode01
import Submission.SixProjectionCode02
import Submission.SixProjectionCode03
import Submission.SixProjectionCode04
import Submission.SixProjectionCode05
import Submission.PureSixComplete0

/-! Connecting actual canonical rows to the pure projected-word coverage check. -/
namespace Erdos184Work.SixCaseCompatibility0
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows0
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma compatible_rows (q0 : Fin 12) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12)
    (h0 : SixProjectionCode00.Compatible q0 q1 q2 q3 q4 q5)
    (h1 : SixProjectionCode01.Compatible q0 q1 q2 q3 q4 q5)
    (h2 : SixProjectionCode02.Compatible q0 q1 q2 q3 q4 q5)
    (h3 : SixProjectionCode03.Compatible q0 q1 q2 q3 q4 q5)
    (h4 : SixProjectionCode04.Compatible q0 q1 q2 q3 q4 q5)
    (h5 : SixProjectionCode05.Compatible q0 q1 q2 q3 q4 q5)
    : PureSixLocalFilter0.Compatible q0 q1 q2 q3 q4 q5 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact PureSixLocalFilter0.forward0 (PureSixLocalFilter0.enc0_0 q1,PureSixLocalFilter0.enc0_1 q2,PureSixLocalFilter0.enc0_2 q3,PureSixLocalFilter0.enc0_3 q4,PureSixLocalFilter0.enc0_4 q5) h0
  · exact PureSixLocalFilter0.forward1 (PureSixLocalFilter0.enc1_0 q0,PureSixLocalFilter0.enc1_1 q2,PureSixLocalFilter0.enc1_2 q3,PureSixLocalFilter0.enc1_3 q4,PureSixLocalFilter0.enc1_4 q5) h1
  · exact PureSixLocalFilter0.forward2 (PureSixLocalFilter0.enc2_0 q0,PureSixLocalFilter0.enc2_1 q1,PureSixLocalFilter0.enc2_2 q3,PureSixLocalFilter0.enc2_3 q4,PureSixLocalFilter0.enc2_4 q5) h2
  · exact PureSixLocalFilter0.forward3 (PureSixLocalFilter0.enc3_0 q0,PureSixLocalFilter0.enc3_1 q1,PureSixLocalFilter0.enc3_2 q2,PureSixLocalFilter0.enc3_3 q4,PureSixLocalFilter0.enc3_4 q5) h3
  · exact PureSixLocalFilter0.forward4 (PureSixLocalFilter0.enc4_0 q0,PureSixLocalFilter0.enc4_1 q1,PureSixLocalFilter0.enc4_2 q2,PureSixLocalFilter0.enc4_3 q3,PureSixLocalFilter0.enc4_4 q5) h4
  · exact PureSixLocalFilter0.forward5 (PureSixLocalFilter0.enc5_0 q0,PureSixLocalFilter0.enc5_1 q1,PureSixLocalFilter0.enc5_2 q2,PureSixLocalFilter0.enc5_3 q3,PureSixLocalFilter0.enc5_4 q4) h5

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    PureSixLocalFilter0.Compatible (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5)) :=
  compatible_rows (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5))
    (SixProjectionCode00.compatible o h)    (SixProjectionCode01.compatible o h)    (SixProjectionCode02.compatible o h)    (SixProjectionCode03.compatible o h)    (SixProjectionCode04.compatible o h)    (SixProjectionCode05.compatible o h)

lemma lookup (o : Orders) (h : LocalBounds b hb o) :
    (PureSixLocalFilter0.output.lookup (SixRows0.key o)).isSome = true := by
  have hh := PureSixLocalFilter0.complete_rows (SixRows0.key0 (o 0)) (SixRows0.key1 (o 1)) (SixRows0.key2 (o 2)) (SixRows0.key3 (o 3)) (SixRows0.key4 (o 4)) (SixRows0.key5 (o 5)) (compatible o h)
  change (PureSixLocalFilter0.output.lookup (PureSixRowModel0.key (rawRows o))).isSome = true at hh
  rwa [key_rawRows] at hh
lemma exists_code (o : Orders) (h : LocalBounds b hb o) :
    ∃ c, PureSixOrbitLookup0.table.lookup (SixRows0.key o) = some c := by
  exact Option.isSome_iff_exists.mp (lookup o h)
#print axioms exists_code
#print axioms src_rawRows
end Erdos184Work.SixCaseCompatibility0
