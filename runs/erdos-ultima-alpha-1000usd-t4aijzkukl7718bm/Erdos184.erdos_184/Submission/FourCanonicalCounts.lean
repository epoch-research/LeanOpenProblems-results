import Submission.FourNumericalPatterns
import Submission.LocalCanonicalRows
import Submission.CanonicalThreeReduction
import Submission.TripleAlternationKernels

/-! Computable canonical versions of the nine numerical four-color patterns,
and the forward form of the four-marker alternation predicate. -/
namespace Erdos184Work.FourCanonicalCounts
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def counts (k : Fin 9) (p : PairIndex 4) : Fin 3 :=
  FourNumericalPatterns.representative k (FourNumericalPatterns.pairIndex p.val.1 p.val.2)

lemma marker_bound : ∀ (k : Fin 9) (i : Fin 4), 2 ≤ (markers (counts k) i).card := by decide +kernel
lemma arity_bound : ∀ (k : Fin 9) (i : Fin 4), arity (counts k) i ≤ 4 := by decide +kernel

abbrev Orders (k : Fin 9) := ∀ i, Marked.Order (arity (counts k) i)

end Erdos184Work.FourCanonicalCounts

namespace Erdos184Work.TripleAlternationKernels
set_option maxHeartbeats 3000000
local instance : Fintype P4 := fintypePerm

def ForwardAlternating (p : Fin 4 → Fin 4) : Prop :=
  ∀ j, (p j).val < 2 ↔ ¬ (p (j+1)).val < 2
instance (p : Fin 4 → Fin 4) : Decidable (ForwardAlternating p) := by
  unfold ForwardAlternating
  infer_instance

lemma alternating_iff_forward : ∀ p : P4, Alternating p ↔ ForwardAlternating p := by decide +kernel

#print axioms alternating_iff_forward
#print axioms Erdos184Work.FourCanonicalCounts.arity_bound
end Erdos184Work.TripleAlternationKernels
