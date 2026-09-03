import Submission.Forest93IntegerData
namespace Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

lemma pivot_degreeNum : 2*degreeNum 192 ≤ denominator ∧ 4*degreeNum 160 ≤ denominator := by decide +kernel
#print axioms pivot_degreeNum
end Erdos7Forest93Certificate
