import Submission.CyclicSeriesData

/-! Exact retained-position certificates for cycles of seven and eight positions.
This is auxiliary finite infrastructure, not a graph decomposition bound. -/
namespace Erdos184Work.LabelKernel.CyclicSeries
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma valid5 : ∀ (s : Finset (Fin 7)) (hs : 2 ≤ s.card), Valid s hs := by decide +kernel
lemma valid6 : ∀ (s : Finset (Fin 8)) (hs : 2 ≤ s.card), Valid s hs := by decide +kernel

lemma valid_le_six {n : ℕ} (hn : n ≤ 6) (s : Finset (Fin (n+2)))
    (hs : 2 ≤ s.card) : Valid s hs := by
  interval_cases n
  · exact valid0 s hs
  · exact valid1 s hs
  · exact valid2 s hs
  · exact valid3 s hs
  · exact valid4 s hs
  · exact valid5 s hs
  · exact valid6 s hs

#print axioms valid5
#print axioms valid6
#print axioms valid_le_six
end Erdos184Work.LabelKernel.CyclicSeries
