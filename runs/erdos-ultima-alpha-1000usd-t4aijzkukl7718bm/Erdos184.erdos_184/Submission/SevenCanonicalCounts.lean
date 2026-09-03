import Submission.FiveCanonicalCounts

/-! The all-single-contact seven-color canonical layout. -/
namespace Erdos184Work.SevenCanonicalCounts
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

def counts (_ : Fin 1) (_ : PairIndex 7) : Fin 3 := 1
lemma marker_bound : ∀ (k : Fin 1) (i : Fin 7), 2 ≤ (markers (counts k) i).card := by decide +kernel
lemma marker_card : ∀ (k : Fin 1) (i : Fin 7), (markers (counts k) i).card = 6 := by decide +kernel
lemma arity_bound : ∀ (k : Fin 1) (i : Fin 7), arity (counts k) i ≤ 4 := by decide +kernel
lemma arity_eq : ∀ (k : Fin 1) (i : Fin 7), arity (counts k) i = 4 := by decide +kernel
abbrev Orders (k : Fin 1) := ∀ i, Marked.Order (arity (counts k) i)
#print axioms marker_bound
#print axioms arity_bound
end Erdos184Work.SevenCanonicalCounts
