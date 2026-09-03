import Submission.Forest93IntegerData
/-! One small, ordinary kernel check for the forest metadata. -/
namespace Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false
private def check0 (i : Index) : Bool := (parent i).elim true (fun j => decide (rank j < rank i))
private lemma checked0 : ∀ i,check0 i = true := by decide +kernel
lemma parent_decreases (i : Index) : (parent i).elim True (fun j => rank j < rank i) := by
  have hh := checked0 i
  cases hp : parent i <;> simpa [check0,hp] using hh
#print axioms parent_decreases
end Erdos7Forest93Certificate
