import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_block0 : ∀ i : Fin 12, ValidAt (0 + i.val) := by decide +kernel
lemma valid_interval0 : FiniteIntervals.Covers ValidAt 0 12 :=
  FiniteIntervals.of_fin 0 12 valid_block0
#print axioms valid_interval0
end Erdos184Work.PureSixActions0
