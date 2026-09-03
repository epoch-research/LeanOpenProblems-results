import Submission.Forest93IntegerData
/-! One small, ordinary kernel check for the forest metadata. -/
namespace Erdos7Forest93Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false
private def check1 (i : Index) : Bool := (parent i).elim true (fun j => decide ((i,j) ∈ edges))
private lemma checked1 : ∀ i,check1 i = true := by decide +kernel
lemma parent_edges (i : Index) : (parent i).elim True (fun j => (i,j) ∈ edges) := by
  have hh := checked1 i
  cases hp : parent i <;> simpa [check1,hp] using hh
#print axioms parent_edges
end Erdos7Forest93Certificate
