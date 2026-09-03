import Submission.FiveProjection02Base

/-! Assembly and local catalogue transport for this four-color projection. -/
open scoped Classical
namespace Erdos184Work.FiveProjection02
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalSubsetCoarsening LocalCanonicalRows CanonicalThreeReduction
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable local instance projectionTheoryDecEq {I : Type*} {m : I → ℕ} :
    DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
lemma edge_apply0 (o : Orders) (j : Fin 3) :
    edgeEquiv o ⟨0,j⟩ = ⟨c0,edgeMap0 (o 0) j⟩ := by
  simp only [edgeEquiv,Equiv.sigmaCongr,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,
    Equiv.sigmaCongrLeft_apply,rowEquiv,Fin.cases_zero,Fin.cases_succ]
  simp only [T,Equiv.ofBijective_apply,color,Matrix.cons_val_zero',Matrix.cons_val_succ',edgeEquiv0]
  dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Equiv.ofBijective]
  all_goals rfl

lemma edge_apply1 (o : Orders) (j : Fin 3) :
    edgeEquiv o ⟨1,j⟩ = ⟨c1,edgeMap1 (o 1) j⟩ := by
  simp only [edgeEquiv,Equiv.sigmaCongr,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,
    Equiv.sigmaCongrLeft_apply,rowEquiv,Fin.cases_zero,Fin.cases_succ]
  simp only [T,Equiv.ofBijective_apply,color,Matrix.cons_val_zero',Matrix.cons_val_succ',edgeEquiv1]
  dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Equiv.ofBijective]
  all_goals rfl

lemma edge_apply2 (o : Orders) (j : Fin 3) :
    edgeEquiv o ⟨2,j⟩ = ⟨c2,edgeMap2 (o 3) j⟩ := by
  simp only [edgeEquiv,Equiv.sigmaCongr,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,
    Equiv.sigmaCongrLeft_apply,rowEquiv,Fin.cases_zero,Fin.cases_succ]
  simp only [T,Equiv.ofBijective_apply,color,Matrix.cons_val_zero',Matrix.cons_val_succ',edgeEquiv2]
  dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Equiv.ofBijective]
  all_goals rfl

lemma edge_apply3 (o : Orders) (j : Fin 3) :
    edgeEquiv o ⟨3,j⟩ = ⟨c3,edgeMap3 (o 4) j⟩ := by
  simp only [edgeEquiv,Equiv.sigmaCongr,Equiv.trans_apply,Equiv.sigmaCongrRight_apply,
    Equiv.sigmaCongrLeft_apply,rowEquiv,Fin.cases_zero,Fin.cases_succ]
  simp only [T,Equiv.ofBijective_apply,color,Matrix.cons_val_zero',Matrix.cons_val_succ',edgeEquiv3]
  dsimp only [DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Equiv.ofBijective]
  all_goals rfl

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
    · change Fin 3 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(0 : Fin 4),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(0 : Fin 4),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(0 : Fin 4),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(0 : Fin 4),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c0,edgeMap0 (o 0) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c0,edgeMap0 (o 0) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply0 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 0 ((SmallOrderNormalization.normalized 1 (smallOrder0 (o 0))).vertex j)),
          phi (fastPlace b₀ hb₀ 0 ((SmallOrderNormalization.normalized 1 (smallOrder0 (o 0))).vertex (j+(1 : Fin 3))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c0 (edgeMap0 (o 0) j),
          StableCanonicalCoarsening.word b hb o A hr c0 (edgeMap0 (o 0) j+(1 : Fin 3)))
      rw [row0_local,row0_local,smallPlace0]
      exact endpoints0_valid (o 0) j
    · change Fin 3 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(1 : Fin 4),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(1 : Fin 4),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(1 : Fin 4),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(1 : Fin 4),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c1,edgeMap1 (o 1) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c1,edgeMap1 (o 1) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply1 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 1 ((SmallOrderNormalization.normalized 1 (smallOrder1 (o 1))).vertex j)),
          phi (fastPlace b₀ hb₀ 1 ((SmallOrderNormalization.normalized 1 (smallOrder1 (o 1))).vertex (j+(1 : Fin 3))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c1 (edgeMap1 (o 1) j),
          StableCanonicalCoarsening.word b hb o A hr c1 (edgeMap1 (o 1) j+(1 : Fin 3)))
      rw [row1_local,row1_local,smallPlace1]
      exact endpoints1_valid (o 1) j
    · change Fin 3 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(2 : Fin 4),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(2 : Fin 4),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(2 : Fin 4),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(2 : Fin 4),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c2,edgeMap2 (o 3) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c2,edgeMap2 (o 3) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply2 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 2 ((SmallOrderNormalization.normalized 1 (smallOrder2 (o 3))).vertex j)),
          phi (fastPlace b₀ hb₀ 2 ((SmallOrderNormalization.normalized 1 (smallOrder2 (o 3))).vertex (j+(1 : Fin 3))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c2 (edgeMap2 (o 3) j),
          StableCanonicalCoarsening.word b hb o A hr c2 (edgeMap2 (o 3) j+(1 : Fin 3)))
      rw [row2_local,row2_local,smallPlace2]
      exact endpoints2_valid (o 3) j
    · change Fin 3 at j
      change s(phi (fastSource b₀ hb₀ (smallOrders o) ⟨(3 : Fin 4),j⟩),
          phi (fastTarget b₀ hb₀ (smallOrders o) ⟨(3 : Fin 4),j⟩)) =
        s(StableCanonicalCoarsening.source b hb o A hr (edgeEquiv o ⟨(3 : Fin 4),j⟩),
          StableCanonicalCoarsening.target b hb o A hr (edgeEquiv o ⟨(3 : Fin 4),j⟩))
      apply Eq.trans (b := s(StableCanonicalCoarsening.source b hb o A hr ⟨c3,edgeMap3 (o 4) j⟩,
        StableCanonicalCoarsening.target b hb o A hr ⟨c3,edgeMap3 (o 4) j⟩))
        ?_ (congrArg (fun e => s(StableCanonicalCoarsening.source b hb o A hr e,
          StableCanonicalCoarsening.target b hb o A hr e)) (edge_apply3 o j).symm)
      simp only [fastSource,fastTarget,StableCanonicalCoarsening.source,StableCanonicalCoarsening.target,
        smallOrders,Fin.cases_zero,Fin.cases_succ]
      change s(phi (fastPlace b₀ hb₀ 3 ((SmallOrderNormalization.normalized 1 (smallOrder3 (o 4))).vertex j)),
          phi (fastPlace b₀ hb₀ 3 ((SmallOrderNormalization.normalized 1 (smallOrder3 (o 4))).vertex (j+(1 : Fin 3))))) =
        s(StableCanonicalCoarsening.word b hb o A hr c3 (edgeMap3 (o 4) j),
          StableCanonicalCoarsening.word b hb o A hr c3 (edgeMap3 (o 4) j+(1 : Fin 3)))
      rw [row3_local,row3_local,smallPlace3]
      exact endpoints3_valid (o 4) j

lemma map_colors (o : Orders) (B : Finset (Fin 4)) :
    (PathSubstitution.Family.colorLabels B).map (embedding o).edge =
      PathSubstitution.Family.colorLabels (B.map T.toEmbedding) :=
  ColoredEmbeddingBounds.colorLabels_map (edgeEquiv o) T (fun _ => rfl) B

lemma localBounds (o : Orders) (h : LocalBounds b hb o) :
    LocalBounds b₀ hb₀ (smallOrders o) :=
  ColoredEmbeddingBounds.localBounds b₀ hb₀ (smallOrders o) b hb o A hr T
    (embedding o) (map_colors o) (fun i => FiveCanonicalCounts.arity_bound 0 i.val) h

lemma catalogue (o : Orders) (h : LocalBounds b hb o) :
    (⟨FourRows2.key (smallOrders o),FourRows2.key_lt (smallOrders o)⟩ :
      Fin 1) ∈ FourRows2.good :=
  FourRows2.catalogue (smallOrders o) (localBounds o h)

#print axioms embedding
#print axioms localBounds
#print axioms catalogue
end Erdos184Work.FiveProjection02
