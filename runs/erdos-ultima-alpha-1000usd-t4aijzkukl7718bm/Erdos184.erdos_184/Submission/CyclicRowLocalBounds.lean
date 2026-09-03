import Submission.ColoredKernelLocalBounds
import Submission.CyclicRowKernel

/-! Color-local bounds are invariant under the checked actions on cyclic rows. -/
namespace Erdos184Work.CyclicRowActions.Action
open LabelKernel
set_option maxHeartbeats 1000000
variable {I W J : Type*} {length choices : I → ℕ} [∀ i, NeZero (length i)]
    {word : ∀ i, Fin (choices i) → Fin (length i) → W}
    [Fintype J] [DecidableEq J] [DecidableEq W] [DecidableEq I]
    (a : Action length choices word) (e : J ≃ Edges length) (q : Rows choices)

lemma flatEdge_color (j : J) : (e (a.flatEdge e q j)).1 = a.color (e j).1 := by
  change (e (e.symm (a.edgeEquiv q (e j)))).1 = _
  rw [e.apply_symm_apply]
  exact a.edge_color q (e j)

lemma colorLocalBounds (h : ColorLocalBounds
    (fun j => source length choices word q (e j))
    (fun j => target length choices word q (e j)) (fun j => (e j).1)) :
    ColorLocalBounds (fun j => source length choices word (a.apply q) (e j))
      (fun j => target length choices word (a.apply q) (e j)) (fun j => (e j).1) :=
  h.transport (a.flatEdge e q) a.color (a.embedding e q) rfl (a.flatEdge_color e q)

#print axioms colorLocalBounds
end Erdos184Work.CyclicRowActions.Action
