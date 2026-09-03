import Submission.CanonicalPairKernel
open Erdos184Work.PairJunctionCoding Erdos184Work.PairSlotMarkers Erdos184Work.CanonicalPairLayout
namespace InspectCanonicalCompute
def b : PairIndex 4 → Fin 3 := fun _ => 1
#reduce markers b 0
#reduce (markers b 0).sort (fun a b => a ≤ b)
#print Finset.sort
#print Multiset.sort
end InspectCanonicalCompute
