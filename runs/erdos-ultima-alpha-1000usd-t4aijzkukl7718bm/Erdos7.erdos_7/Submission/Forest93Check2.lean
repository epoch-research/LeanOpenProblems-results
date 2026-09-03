import Submission.Forest93IntegerData
namespace Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

lemma edges_parent_checked : ∀ e : edges,parent e.val.1 = some e.val.2 := by decide +kernel
#print axioms edges_parent_checked
end Erdos7Forest93Certificate
