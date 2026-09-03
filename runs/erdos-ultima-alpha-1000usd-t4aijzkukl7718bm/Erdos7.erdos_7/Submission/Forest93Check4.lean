import Submission.Forest93IntegerData
namespace Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

lemma forced_mem : forced ∈ edges := by decide +kernel
#print axioms forced_mem
end Erdos7Forest93Certificate
