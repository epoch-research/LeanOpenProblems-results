import FormalConjecturesUtil
import Submission.C8CentralSuzukiRow0
import Submission.C8CentralSuzukiRow1
import Submission.C8CentralSuzukiRow2
import Submission.C8CentralSuzukiRow3

/-! A rational octagon identity for opposite twisted central matrices. -/
namespace Erdos713C8CentralSuzukiMatrices
open Erdos713C8MixedSuzukiMatrices
variable {F : Type*} [Field F] [CharP F 2]
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

lemma word_identity (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (hc : c ≠ 0) (hJ : J σ c ≠ 0) (hA : A σ c ≠ 0) :
    Z σ 1*O σ 1*Z σ c*O σ (d σ c)*Z σ (h σ c) =
      O σ (e σ c)*Z σ (f σ c)*O σ (g σ c) := by
  ext i j
  fin_cases i
  · exact word_row0 σ hσ c hc hJ hA j
  · exact word_row1 σ hσ c hc hJ hA j
  · exact word_row2 σ hσ c hc hJ hA j
  · exact word_row3 σ hσ c hc hJ hA j

end Erdos713C8CentralSuzukiMatrices
