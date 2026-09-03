import Submission.PetersenBaseData
import Submission.FinsetMask
import Submission.FiniteIntervals

/-! Exhaustive finite support checks for the Petersen cycle catalogue. -/
namespace Erdos184Work.PetersenBase
open Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def ContainsCycle (j : ℕ) : Prop :=
  (FinsetMask.word 15 j).Nonempty → code.valid (FinsetMask.word 15 j) →
    ∃ i : Fin 57, edges i ⊆ FinsetMask.word 15 j

instance (j : ℕ) : Decidable (ContainsCycle j) := by
  unfold ContainsCycle
  infer_instance

lemma check0 : ∀ i : Fin 1024, ContainsCycle i.val := by decide +kernel
#print axioms check0
end Erdos184Work.PetersenBase
