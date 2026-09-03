import Submission.SixProjection14Base

/-! Assembly and local catalogue transport for this five-color projection. -/
open scoped Classical
namespace Erdos184Work.SixProjection14
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable local instance projectionTheoryDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
lemma edge_apply0 (o : Orders) (j : Fin 5) :
    edgeEquiv o ⟨0,j⟩ = ⟨c0,edgeMap0 (o 0) j⟩ := by
  apply Eq.trans (edge_apply_generic o 0 j)
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike]
    have hh := congrArg Equiv.toFun (row_apply0 o)
    dsimp only [edgeEquiv0,Equiv.ofBijective] at hh
    exact congrFun hh j

lemma row_apply1 (o : Orders) : rowEquiv o 1 = edgeEquiv1 (o 1) := by
  change rowEquiv o ((0 : Fin 4).succ) = edgeEquiv1 (o 1)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]

lemma edge_apply1 (o : Orders) (j : Fin 5) :
    edgeEquiv o ⟨1,j⟩ = ⟨c1,edgeMap1 (o 1) j⟩ := by
  apply Eq.trans (edge_apply_generic o 1 j)
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike]
    have hh := congrArg Equiv.toFun (row_apply1 o)
    dsimp only [edgeEquiv1,Equiv.ofBijective] at hh
    exact congrFun hh j

lemma row_apply2 (o : Orders) : rowEquiv o 2 = edgeEquiv2 (o 2) := by
  change rowEquiv o ((0 : Fin 3).succ.succ) = edgeEquiv2 (o 2)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]

lemma edge_apply2 (o : Orders) (j : Fin 4) :
    edgeEquiv o ⟨2,j⟩ = ⟨c2,edgeMap2 (o 2) j⟩ := by
  apply Eq.trans (edge_apply_generic o 2 j)
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike]
    have hh := congrArg Equiv.toFun (row_apply2 o)
    dsimp only [edgeEquiv2,Equiv.ofBijective] at hh
    exact congrFun hh j

lemma row_apply3 (o : Orders) : rowEquiv o 3 = edgeEquiv3 (o 3) := by
  change rowEquiv o ((0 : Fin 2).succ.succ.succ) = edgeEquiv3 (o 3)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]

lemma edge_apply3 (o : Orders) (j : Fin 4) :
    edgeEquiv o ⟨3,j⟩ = ⟨c3,edgeMap3 (o 3) j⟩ := by
  apply Eq.trans (edge_apply_generic o 3 j)
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike]
    have hh := congrArg Equiv.toFun (row_apply3 o)
    dsimp only [edgeEquiv3,Equiv.ofBijective] at hh
    exact congrFun hh j

lemma row_apply4 (o : Orders) : rowEquiv o 4 = edgeEquiv4 (o 5) := by
  change rowEquiv o ((0 : Fin 1).succ.succ.succ.succ) = edgeEquiv4 (o 5)
  simp only [rowEquiv,Fin.cases_zero,Fin.cases_succ]

lemma edge_apply4 (o : Orders) (j : Fin 4) :
    edgeEquiv o ⟨4,j⟩ = ⟨c4,edgeMap4 (o 5) j⟩ := by
  apply Eq.trans (edge_apply_generic o 4 j)
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike]
    have hh := congrArg Equiv.toFun (row_apply4 o)
    dsimp only [edgeEquiv4,Equiv.ofBijective] at hh
    exact congrFun hh j

noncomputable def embedding (o : Orders) :
    Embedding (source b₀ hb₀ (smallOrders o)) (target b₀ hb₀ (smallOrders o))
      (StableCanonicalCoarsening.source b hb o A hr) (StableCanonicalCoarsening.target b hb o A hr) where
  edge := (edgeEquiv o).toEmbedding
  vertex := ⟨phi,phi_injective⟩
  endpoints e := by
    rcases e with ⟨i,j⟩
    rw [source_eq_fast,target_eq_fast]
    simp only [Equiv.toEmbedding_apply,Function.Embedding.coeFn_mk]
    fin_cases i
    · change Fin 5 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(0 : Fin 5),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(0 : Fin 5),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(0 : Fin 5),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(0 : Fin 5),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c0,edgeMap0 (o 0) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c0,edgeMap0 (o 0) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply0 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (o 0))).vertex j)),
          phi (fastPlace b₀ hb₀ 0 ((SmallOrderNormalization.normalized 3 (smallOrder0 (o 0))).vertex (j+(1 : Fin 5))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c0 (edgeMap0 (o 0) j),
          StableCanonicalCoarsening.word b hb o A hr c0 (edgeMap0 (o 0) j+(1 : Fin 5)))
      rw [row0_local,row0_local,smallPlace0]
      exact endpoints0_valid (o 0) j
    · change Fin 5 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(1 : Fin 5),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(1 : Fin 5),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(1 : Fin 5),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(1 : Fin 5),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c1,edgeMap1 (o 1) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c1,edgeMap1 (o 1) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply1 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 1 ((SmallOrderNormalization.normalized 3 (smallOrder1 (o 1))).vertex j)),
          phi (fastPlace b₀ hb₀ 1 ((SmallOrderNormalization.normalized 3 (smallOrder1 (o 1))).vertex (j+(1 : Fin 5))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c1 (edgeMap1 (o 1) j),
          StableCanonicalCoarsening.word b hb o A hr c1 (edgeMap1 (o 1) j+(1 : Fin 5)))
      rw [row1_local,row1_local,smallPlace1]
      exact endpoints1_valid (o 1) j
    · change Fin 4 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(2 : Fin 5),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(2 : Fin 5),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(2 : Fin 5),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(2 : Fin 5),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c2,edgeMap2 (o 2) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c2,edgeMap2 (o 2) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply2 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 2 ((SmallOrderNormalization.normalized 2 (smallOrder2 (o 2))).vertex j)),
          phi (fastPlace b₀ hb₀ 2 ((SmallOrderNormalization.normalized 2 (smallOrder2 (o 2))).vertex (j+(1 : Fin 4))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c2 (edgeMap2 (o 2) j),
          StableCanonicalCoarsening.word b hb o A hr c2 (edgeMap2 (o 2) j+(1 : Fin 4)))
      rw [row2_local,row2_local,smallPlace2]
      exact endpoints2_valid (o 2) j
    · change Fin 4 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(3 : Fin 5),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(3 : Fin 5),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(3 : Fin 5),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(3 : Fin 5),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c3,edgeMap3 (o 3) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c3,edgeMap3 (o 3) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply3 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 3 ((SmallOrderNormalization.normalized 2 (smallOrder3 (o 3))).vertex j)),
          phi (fastPlace b₀ hb₀ 3 ((SmallOrderNormalization.normalized 2 (smallOrder3 (o 3))).vertex (j+(1 : Fin 4))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c3 (edgeMap3 (o 3) j),
          StableCanonicalCoarsening.word b hb o A hr c3 (edgeMap3 (o 3) j+(1 : Fin 4)))
      rw [row3_local,row3_local,smallPlace3]
      exact endpoints3_valid (o 3) j
    · change Fin 4 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(4 : Fin 5),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(4 : Fin 5),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(4 : Fin 5),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(4 : Fin 5),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c4,edgeMap4 (o 5) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c4,edgeMap4 (o 5) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply4 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 4 ((SmallOrderNormalization.normalized 2 (smallOrder4 (o 5))).vertex j)),
          phi (fastPlace b₀ hb₀ 4 ((SmallOrderNormalization.normalized 2 (smallOrder4 (o 5))).vertex (j+(1 : Fin 4))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c4 (edgeMap4 (o 5) j),
          StableCanonicalCoarsening.word b hb o A hr c4 (edgeMap4 (o 5) j+(1 : Fin 4)))
      rw [row4_local,row4_local,smallPlace4]
      exact endpoints4_valid (o 5) j

lemma map_colors (o : Orders) (B : Finset (Fin 5)) :
    (PathSubstitution.Family.colorLabels B).map (embedding o).edge =
      PathSubstitution.Family.colorLabels (B.map T.toEmbedding) :=
  ColoredEmbeddingBounds.colorLabels_map (edgeEquiv o) T (fun _ => rfl) B

lemma localBounds (o : Orders) (h : LocalBounds b hb o) :
    LocalBounds b₀ hb₀ (smallOrders o) :=
  ColoredEmbeddingBounds.localBounds_large b₀ hb₀ (smallOrders o) b hb o A hr T
    (embedding o) (map_colors o) (fun i => (SixCanonicalCounts.arity_bound 1 i.val).trans (by decide)) h

lemma catalogue (o : Orders) (h : LocalBounds b hb o) :
    (⟨FiveRows1.key (smallOrders o),FiveRows1.key_lt (smallOrders o)⟩ :
      Fin 3888) ∈ FiveRows1.good :=
  FiveRows1.catalogue (smallOrders o) (localBounds o h)

#print axioms embedding
#print axioms localBounds
#print axioms catalogue
end Erdos184Work.SixProjection14
