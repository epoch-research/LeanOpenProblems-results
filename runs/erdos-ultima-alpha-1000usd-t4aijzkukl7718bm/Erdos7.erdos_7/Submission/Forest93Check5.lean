import Submission.Forest93IntegerData
namespace Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

lemma coefficient_divides : ∀ e : edges,e.val ≠ forced →
    denominator ∣ weightNum e.val.1*weightNum e.val.2 := by decide +kernel
#print axioms coefficient_divides
end Erdos7Forest93Certificate
