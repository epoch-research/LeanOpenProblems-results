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



#eval IO.FS.writeFile "/tmp/code41-current-command" "begin row2"
lemma row2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder2 q)).vertex =
      FiveRows1.words2 (FiveRows1.key2 (smallOrder2 q)) →
    enc2 (SixRows4.key3 q) = (FiveRows1.key2 (smallOrder2 q)).val + 1 := by decide +kernel

#eval IO.FS.writeFile "/tmp/code41-current-command" "begin row3"
lemma row3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex =
      FiveRows1.words3 (FiveRows1.key3 (smallOrder3 q)) →
    enc3 (SixRows4.key4 q) = (FiveRows1.key3 (smallOrder3 q)).val + 1 := by decide +kernel

#eval IO.FS.writeFile "/tmp/code41-current-command" "begin row4"
lemma row4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex =
      FiveRows1.words4 (FiveRows1.key4 (smallOrder4 q)) →
    enc4 (SixRows4.key5 q) = (FiveRows1.key4 (smallOrder4 q)).val + 1 := by decide +kernel


end Erdos184Work.SixProjectionCode41
