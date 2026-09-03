import Submission.Forest93IntegerData
namespace Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

lemma total_checked : certificateTotal = 89947776 := by decide +kernel

#print axioms total_checked
end Erdos7Forest93Certificate
