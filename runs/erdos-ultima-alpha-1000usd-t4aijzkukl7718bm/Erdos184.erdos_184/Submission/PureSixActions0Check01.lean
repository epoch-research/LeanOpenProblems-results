import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_block1 : ∀ i : Fin 12, ValidAt (12 + i.val) := by decide +kernel
lemma valid_interval1 : FiniteIntervals.Covers ValidAt 12 24 :=
  FiniteIntervals.of_fin 12 12 valid_block1
#print axioms valid_interval1
end Erdos184Work.PureSixActions0
