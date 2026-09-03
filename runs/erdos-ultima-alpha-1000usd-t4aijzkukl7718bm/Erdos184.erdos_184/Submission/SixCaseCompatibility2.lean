import Submission.SixRawBridge2
import Submission.SixProjectionCode20
import Submission.SixProjectionCode21
import Submission.SixProjectionCode22
import Submission.SixProjectionCode23
import Submission.SixProjectionCode24
import Submission.SixProjectionCode25
import Submission.PureSixComplete2

/-! Connecting actual canonical rows to the pure projected-word coverage check. -/
namespace Erdos184Work.SixCaseCompatibility2
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixRows2
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma compatible_rows (q0 : Fin 60) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 60) (q4 : Fin 12) (q5 : Fin 12)
    (h0 : SixProjectionCode20.Compatible q0 q1 q2 q3 q4 q5)
    (h1 : SixProjectionCode21.Compatible q0 q1 q2 q3 q4 q5)
    (h2 : SixProjectionCode22.Compatible q0 q1 q2 q3 q4 q5)
    (h3 : SixProjectionCode23.Compatible q0 q1 q2 q3 q4 q5)
    (h4 : SixProjectionCode24.Compatible q0 q1 q2 q3 q4 q5)
    (h5 : SixProjectionCode25.Compatible q0 q1 q2 q3 q4 q5)
    : PureSixLocalFilter2.Compatible q0 q1 q2 q3 q4 q5 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact PureSixLocalFilter2.forward0 (PureSixLocalFilter2.enc0_0 q2,PureSixLocalFilter2.enc0_1 q3,PureSixLocalFilter2.enc0_2 q1,PureSixLocalFilter2.enc0_3 q4,PureSixLocalFilter2.enc0_4 q5) h0
  · exact PureSixLocalFilter2.forward1 (PureSixLocalFilter2.enc1_0 q2,PureSixLocalFilter2.enc1_1 q3,PureSixLocalFilter2.enc1_2 q0,PureSixLocalFilter2.enc1_3 q4,PureSixLocalFilter2.enc1_4 q5) h1
  · exact PureSixLocalFilter2.forward2 (PureSixLocalFilter2.enc2_0 q0,PureSixLocalFilter2.enc2_1 q1,PureSixLocalFilter2.enc2_2 q3,PureSixLocalFilter2.enc2_3 q4,PureSixLocalFilter2.enc2_4 q5) h2
  · exact PureSixLocalFilter2.forward3 (PureSixLocalFilter2.enc3_0 q0,PureSixLocalFilter2.enc3_1 q1,PureSixLocalFilter2.enc3_2 q2,PureSixLocalFilter2.enc3_3 q4,PureSixLocalFilter2.enc3_4 q5) h3
  · exact PureSixLocalFilter2.forward4 (PureSixLocalFilter2.enc4_0 q0,PureSixLocalFilter2.enc4_1 q1,PureSixLocalFilter2.enc4_2 q2,PureSixLocalFilter2.enc4_3 q3,PureSixLocalFilter2.enc4_4 q5) h4
  · exact PureSixLocalFilter2.forward5 (PureSixLocalFilter2.enc5_0 q0,PureSixLocalFilter2.enc5_1 q1,PureSixLocalFilter2.enc5_2 q2,PureSixLocalFilter2.enc5_3 q3,PureSixLocalFilter2.enc5_4 q4) h5

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    PureSixLocalFilter2.Compatible (SixRows2.key0 (o 0)) (SixRows2.key1 (o 1)) (SixRows2.key2 (o 2)) (SixRows2.key3 (o 3)) (SixRows2.key4 (o 4)) (SixRows2.key5 (o 5)) :=
  compatible_rows (SixRows2.key0 (o 0)) (SixRows2.key1 (o 1)) (SixRows2.key2 (o 2)) (SixRows2.key3 (o 3)) (SixRows2.key4 (o 4)) (SixRows2.key5 (o 5))
    (SixProjectionCode20.compatible o h)    (SixProjectionCode21.compatible o h)    (SixProjectionCode22.compatible o h)    (SixProjectionCode23.compatible o h)    (SixProjectionCode24.compatible o h)    (SixProjectionCode25.compatible o h)

lemma lookup (o : Orders) (h : LocalBounds b hb o) :
    (PureSixLocalFilter2.output.lookup (SixRows2.key o)).isSome = true := by
  have hh := PureSixLocalFilter2.complete_rows (SixRows2.key0 (o 0)) (SixRows2.key1 (o 1)) (SixRows2.key2 (o 2)) (SixRows2.key3 (o 3)) (SixRows2.key4 (o 4)) (SixRows2.key5 (o 5)) (compatible o h)
  change (PureSixLocalFilter2.output.lookup (PureSixRowModel2.key (rawRows o))).isSome = true at hh
  rwa [key_rawRows] at hh
lemma exists_code (o : Orders) (h : LocalBounds b hb o) :
    ∃ c, PureSixOrbitLookup2.table.lookup (SixRows2.key o) = some c := by
  exact Option.isSome_iff_exists.mp (lookup o h)
#print axioms exists_code
#print axioms src_rawRows
end Erdos184Work.SixCaseCompatibility2
