import Submission.TreeParityKernel
import Submission.TreeCutAbsorption

set_option autoImplicit false

open Finset SimpleGraph Classical

namespace ErdosSosCutReduction

universe u v

/-- The independently proved tree-kernel certificate supplies exactly the
interface used by the cut-extension theorem. -/
lemma kernelData {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ}
    {R U W : Finset V} (h : TreeParityKernel.IsParityKernel T c R U W) :
    TreeCutAbsorption.KernelData T c R U W :=
  ⟨h.disjointRU, h.disjointRW, h.disjointUW, h.partition, h.nonempty,
    h.connected, h.independent, h.neighbors, h.odd_le, h.outside_ge⟩

/-- Exact parameter-decreasing Erdős–Sós reduction for a density-funded cut.
The tree kernel is constructed, not assumed. The remaining hypotheses are
explicit host-cut conditions and the smaller-parameter induction hypothesis. -/
theorem isContained_of_cut {V : Type u} [Fintype V] {H : Type v} [Fintype H]
    (T : SimpleGraph V) (G : SimpleGraph H) (hT : T.IsTree) {k c : ℕ}
    (hk : T.edgeFinset.card = k) (hc : 1 ≤ c) (hck : c ≤ k / 2)
    {A B : Finset H} (hcut : TreeCutAbsorption.HostCut G k c A B)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card H < (G.edgeFinset.card : ℚ))
    (hbudget : (G.interedges A B).card - (c : ℚ) * B.card ≤
      ((k : ℚ) - 1) / 2 * A.card - (G.induce (A : Set H)).edgeFinset.card)
    (ih : ∀ m < k, TreeCutAbsorption.StrictESUpTo.{u, v} m) :
    T.IsContained G := by
  obtain ⟨R, U, W, hK, _⟩ := TreeParityKernel.parity_kernel hT hk hc hck
  exact TreeCutAbsorption.conditional_erdos_sos T G hT hk hc
    ⟨R, U, W, kernelData hK⟩ hcut hdensity hbudget ih

end ErdosSosCutReduction

#print axioms ErdosSosCutReduction.isContained_of_cut
