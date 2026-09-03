import Submission.CyclicRowActions
import Submission.LabelKernelEmbedding

/-! Transporting the checked row actions to labelled circuit kernels. -/
namespace Erdos184Work.CyclicRowActions.Action
open LabelKernel
set_option maxHeartbeats 1000000
variable {I W J : Type*} {length choices : I → ℕ} [∀ i, NeZero (length i)]
    {word : ∀ i, Fin (choices i) → Fin (length i) → W}
    [DecidableEq J] [DecidableEq W]
    (a : Action length choices word) (e : J ≃ Edges length) (q : Rows choices)

def flatEdge : J ≃ J := (e.trans (a.edgeEquiv q)).trans e.symm

def embedding : Embedding (fun j => source length choices word q (e j))
    (fun j => target length choices word q (e j))
    (fun j => source length choices word (a.apply q) (e j))
    (fun j => target length choices word (a.apply q) (e j)) where
  edge := (a.flatEdge e q).toEmbedding
  vertex := a.vertex
  endpoints j := by
    change s(a.vertex (source length choices word q (e j)),
      a.vertex (target length choices word q (e j))) =
      s(source length choices word (a.apply q) (e (e.symm (a.edgeEquiv q (e j)))),
        target length choices word (a.apply q) (e (e.symm (a.edgeEquiv q (e j)))))
    rw [e.apply_symm_apply]
    exact a.endpoints_apply q (e j)

lemma map_univ [Fintype J] : (Finset.univ : Finset J).map (a.embedding e q).edge = Finset.univ :=
  Finset.map_univ_equiv (a.flatEdge e q)

#print axioms embedding
#print axioms map_univ
end Erdos184Work.CyclicRowActions.Action
