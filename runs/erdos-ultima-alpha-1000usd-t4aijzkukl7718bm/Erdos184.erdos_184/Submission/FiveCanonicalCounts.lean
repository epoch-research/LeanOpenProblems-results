import Submission.FiveSubfamilyPatterns

/-! Canonical multiplicities and marker bounds for the five-color patterns. -/
namespace Erdos184Work.FiveCanonicalCounts
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def counts (k : Fin 5) (p : PairIndex 5) : Fin 3 :=
  ⟨1 + (FiveNumericalPatterns.representative k
    (FiveNumericalPatterns.pairIndex p.val.1 p.val.2)).toNat,by
      generalize FiveNumericalPatterns.representative k
        (FiveNumericalPatterns.pairIndex p.val.1 p.val.2) = b
      cases b <;> decide⟩

lemma marker_bound : ∀ (k : Fin 5) (i : Fin 5), 2 ≤ (markers (counts k) i).card := by
  decide +kernel
lemma marker_lower : ∀ (k : Fin 5) (i : Fin 5), 4 ≤ (markers (counts k) i).card := by
  decide +kernel
lemma marker_upper : ∀ (k : Fin 5) (i : Fin 5), (markers (counts k) i).card ≤ 6 := by
  decide +kernel
lemma arity_bound : ∀ (k : Fin 5) (i : Fin 5), arity (counts k) i ≤ 4 := by
  decide +kernel

abbrev Orders (k : Fin 5) := ∀ i, Marked.Order (arity (counts k) i)

#print axioms marker_bound
#print axioms marker_upper
#print axioms arity_bound
end Erdos184Work.FiveCanonicalCounts
