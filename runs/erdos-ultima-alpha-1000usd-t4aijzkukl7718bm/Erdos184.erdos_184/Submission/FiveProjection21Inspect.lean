import Submission.FiveProjection21Base

/-! Assembly and local catalogue transport for this four-color projection. -/
open scoped Classical
namespace Erdos184Work.FiveProjection21
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable local instance projectionTheoryDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
lemma inspect_generic (o : Orders) (i : Fin 4) (j : Fin (arity b₀ i+2)) :
    edgeEquiv o ⟨i,j⟩ = ⟨T i,rowEquiv o i j⟩ := rfl

lemma inspect_row2 (o : Orders) : rowEquiv o 2 = edgeEquiv2 (o 0) := by
  change rowEquiv o ((0 : Fin 2).succ.succ) = edgeEquiv2 (o 0)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]

lemma inspect_edge_apply2 (o : Orders) (j : Fin 4) :
    edgeEquiv o ⟨2,j⟩ = ⟨c2,edgeMap2 (o 0) j⟩ := by
  apply Eq.trans (inspect_generic o 2 j)
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike]
    have hh := congrArg Equiv.toFun (inspect_row2 o)
    dsimp only [edgeEquiv2,Equiv.ofBijective] at hh
    exact congrFun hh j

#print axioms inspect_edge_apply2
end Erdos184Work.FiveProjection21
