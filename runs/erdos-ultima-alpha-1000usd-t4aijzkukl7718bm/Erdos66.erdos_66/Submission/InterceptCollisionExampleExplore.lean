import Submission.InterceptCurveExplore

/-! An exact finite example distinguishing parameter multiplicities from
the representation count of the union of intercept parabolas. -/
namespace Erdos66InterceptCollisionExample
open Erdos66InterceptCurve Erdos66OriginRepair
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem actual_count_two : pairCount (curveUnion ({1,2} : Finset (ZMod 7)))
    (curveUnion ({1,2} : Finset (ZMod 7))) (6,0)=2 := by
  decide +kernel

theorem weighted_count_eight : weightedCount ({1,2} : Finset (ZMod 7)) {1,2} 0 6=8 := by
  decide +kernel

end Erdos66InterceptCollisionExample
