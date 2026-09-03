import Submission.FiveCanonicalCounts
import Submission.PureSixDoubleTransfer

/-! Canonical six-color multiplicities with their row-size bounds. -/
namespace Erdos184Work.SixCanonicalCounts
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false

def counts (k : Fin 5) (p : PairIndex 6) : Fin 3 :=
  ⟨1 + (PureSixDoublePatterns.representative k
    (PureSixDoublePatterns.pairIndex p.val.1 p.val.2)).toNat,by
      generalize PureSixDoublePatterns.representative k
        (PureSixDoublePatterns.pairIndex p.val.1 p.val.2) = b
      cases b <;> decide⟩
lemma marker_bound : ∀ (k : Fin 5) (i : Fin 6), 2 ≤ (markers (counts k) i).card := by decide +kernel
lemma marker_lower : ∀ (k : Fin 5) (i : Fin 6), 5 ≤ (markers (counts k) i).card := by decide +kernel
lemma marker_upper : ∀ (k : Fin 5) (i : Fin 6), (markers (counts k) i).card ≤ 7 := by decide +kernel
lemma arity_bound : ∀ (k : Fin 5) (i : Fin 6), arity (counts k) i ≤ 5 := by decide +kernel
abbrev Orders (k : Fin 5) := ∀ i, Marked.Order (arity (counts k) i)
#print axioms marker_bound
#print axioms arity_bound
end Erdos184Work.SixCanonicalCounts
