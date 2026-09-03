import Submission.SixProjectionCode41RowsBase
/-! Projection normalization in24-order kernel checks. -/
namespace Erdos184Work.SixProjectionCode41
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection41
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

lemma row1_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows1.words1 (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows1.words1 (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows1.words1 (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row1_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows1.words1 (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))) →
    enc1 (SixRows4.key2 (q,(Sum.inl (Sum.inr ())))) = (FiveRows1.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row1_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inr ())))).vertex =
      FiveRows1.words1 (FiveRows1.key1 (smallOrder1 (q,(Sum.inr ())))) →
    enc1 (SixRows4.key2 (q,(Sum.inr ()))) = (FiveRows1.key1 (smallOrder1 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row1 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder1 q)).vertex =
      FiveRows1.words1 (FiveRows1.key1 (smallOrder1 q)) →
    enc1 (SixRows4.key2 q) = (FiveRows1.key1 (smallOrder1 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row1_0 q
  · exact row1_1 q
  · exact row1_2 q
  · exact row1_3 q
  · exact row1_4 q
#print axioms row1
end Erdos184Work.SixProjectionCode41
