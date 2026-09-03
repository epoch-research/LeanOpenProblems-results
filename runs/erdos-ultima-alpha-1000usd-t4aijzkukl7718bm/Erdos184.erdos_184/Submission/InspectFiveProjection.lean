import Submission.FiveProjection04Base

/-! Assembly of the four-color projection kernel embedding. -/
open scoped Classical
namespace Erdos184Work.FiveProjection04
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance projectionTheoryDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
lemma inspect_edge0 (o : Orders) (j : Fin 3) :
    edgeEquiv o ⟨0,j⟩ = ⟨c0,edgeMap0 (o 0) j⟩ := by
  simp only [edgeEquiv,Equiv.sigmaCongr,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,
    Equiv.sigmaCongrLeft_apply]
  simp only [rowEquiv,Fin.cases_zero]
  simp only [T,Equiv.ofBijective_apply,color,Matrix.cons_val_zero,edgeEquiv0]
  dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Equiv.ofBijective]
  rfl
lemma inspect_order0 (o : Orders) : smallOrders o 0 = smallOrder0 (o 0) := by rfl
lemma inspect_src0 (o : Orders) (j : Fin 3) :
    fastSource b₀ hb₀ (smallOrders o) ⟨0,j⟩ =
      fastPlace b₀ hb₀ 0 ((SmallOrderNormalization.normalized 1 (smallOrder0 (o 0))).vertex j) := by rfl
lemma inspect_dst0 (o : Orders) (j : Fin 3) :
    fastTarget b₀ hb₀ (smallOrders o) ⟨0,j⟩ =
      fastPlace b₀ hb₀ 0 ((SmallOrderNormalization.normalized 1 (smallOrder0 (o 0))).vertex (j+(1 : Fin 3))) := by rfl
#print axioms inspect_edge0
#print axioms inspect_dst0
end Erdos184Work.FiveProjection04
