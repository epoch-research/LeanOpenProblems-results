import Submission.SixProjectionCode41RowsBase
/-! Projection normalization in24-order kernel checks. -/
namespace Erdos184Work.SixProjectionCode41
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection41
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

lemma row0_0_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_0_0 q
  · exact row0_0_1 q
  · exact row0_0_2 q
  · exact row0_0_3 q
  · exact row0_0_4 q
lemma row0_1_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_1_0 q
  · exact row0_1_1 q
  · exact row0_1_2 q
  · exact row0_1_3 q
  · exact row0_1_4 q
lemma row0_2_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_2_0 q
  · exact row0_2_1 q
  · exact row0_2_2 q
  · exact row0_2_3 q
  · exact row0_2_4 q
lemma row0_3_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_3_0 q
  · exact row0_3_1 q
  · exact row0_3_2 q
  · exact row0_3_3 q
  · exact row0_3_4 q
lemma row0_4_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ())))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ())))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ())))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ())))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ())))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inr ())))) = (FiveRows1.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_4_0 q
  · exact row0_4_1 q
  · exact row0_4_2 q
  · exact row0_4_3 q
  · exact row0_4_4 q
lemma row0_5_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ()))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ()))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ()))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ()))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inr ()))) = (FiveRows1.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder0 (q,(Sum.inr ())))).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 (q,(Sum.inr ())))) →
    enc0 (SixRows4.key0 (q,(Sum.inr ()))) = (FiveRows1.key0 (smallOrder0 (q,(Sum.inr ())))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_5_0 q
  · exact row0_5_1 q
  · exact row0_5_2 q
  · exact row0_5_3 q
  · exact row0_5_4 q
lemma row0 : ∀ q : Marked.Order 5,
    (SmallOrderNormalization.normalized 3 (smallOrder0 q)).vertex =
      FiveRows1.words0 (FiveRows1.key0 (smallOrder0 q)) →
    enc0 (SixRows4.key0 q) = (FiveRows1.key0 (smallOrder0 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_0 q
  · exact row0_1 q
  · exact row0_2 q
  · exact row0_3 q
  · exact row0_4 q
  · exact row0_5 q
#print axioms row0
end Erdos184Work.SixProjectionCode41
