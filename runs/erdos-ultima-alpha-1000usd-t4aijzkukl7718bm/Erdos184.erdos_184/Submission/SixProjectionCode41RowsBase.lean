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

def enc0 : Fin 360 → ℕ := ![1,2,3,4,5,6,7,8,9,6,10,4,11,10,12,5,8,2,12,9,11,3,7,1,6,4,5,2,3,1,8,7,12,1,11,2,10,11,9,3,7,4,9,12,10,5,8,6,4,6,10,8,9,7,2,1,11,7,12,8,5,12,3,9,1,6,3,11,5,10,2,4,2,5,8,10,12,11,4,3,7,11,9,10,6,9,1,12,3,5,1,7,6,8,4,2,1,3,7,9,11,12,6,5,8,12,10,9,4,10,2,11,5,3,2,8,4,7,6,1,1,2,3,4,5,6,7,8,9,6,10,4,11,10,12,5,8,2,12,9,11,3,7,1,1,2,3,4,5,6,1,2,1,2,3,4,3,4,5,6,5,6,7,8,9,6,10,4,7,8,7,8,9,6,9,6,10,4,10,4,11,10,12,5,8,2,11,10,11,10,12,5,12,5,8,2,8,2,12,9,11,3,7,1,12,9,12,9,11,3,11,3,7,1,7,1,6,4,5,2,3,1,8,7,12,11,10,11,9,7,9,12,10,8,6,4,5,2,3,1,6,4,6,4,5,2,5,2,3,1,3,1,8,7,12,11,8,7,8,7,12,12,11,11,10,11,9,7,10,11,10,11,9,9,7,7,9,12,10,8,9,12,9,12,10,10,8,8,4,6,10,9,2,1,11,12,5,3,3,5,4,6,10,9,4,6,4,6,10,10,9,9,2,1,11,12,2,1,2,1,11,11,12,12,5,3,5,5,3,3,3,5,3,3,5,5,2,8,4,7,6,1,2,8,2,2,8,8,4,7,4,4,7,7,6,1,6,6,1,1]
def enc1 : Fin 60 → ℕ := ![1,2,3,4,5,6,1,2,1,1,2,2,3,4,3,3,4,4,5,6,5,5,6,6,1,2,3,4,5,6,7,8,9,10,11,10,12,8,12,9,11,7,7,8,7,8,7,8,9,10,9,9,10,10,11,11,11,12,12,12]
def enc2 : Fin 12 → ℕ := ![1,2,3,2,3,1,1,2,1,2,3,3]
def enc3 : Fin 12 → ℕ := ![1,2,3,2,3,1,1,2,1,2,3,3]
def enc4 : Fin 12 → ℕ := ![1,2,3,2,3,1,1,2,1,2,3,3]
end Erdos184Work.SixProjectionCode41
