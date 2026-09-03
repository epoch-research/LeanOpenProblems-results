import Submission.FiniteIntervals
import Submission.SixProjection43
import Submission.SixRows4
import Submission.FiveWordOrbits2

/-! Computable raw-row necessary conditions obtained from a checked projection. -/
namespace Erdos184Work.SixProjectionCode43
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open CanonicalThreeReduction SixProjection43
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def enc0 : Fin 360 → ℕ := ![1,2,1,1,2,2,1,2,3,4,5,6,3,3,3,4,4,4,5,5,5,6,6,6,7,8,7,7,8,8,7,8,9,10,11,12,9,9,9,10,10,10,11,11,11,12,12,12,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,13,13,13,14,14,14,15,15,15,16,16,16,13,14,15,16,17,18,17,17,18,18,17,18,19,19,19,20,20,20,21,21,21,22,22,22,19,20,21,22,23,24,23,23,24,24,23,24,25,26,25,25,26,26,25,26,27,28,29,30,27,27,27,28,28,28,29,29,29,30,30,30,31,32,31,31,32,32,31,32,33,34,33,33,33,24,34,34,34,18,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,35,35,35,36,36,36,37,37,37,22,35,36,37,38,38,38,12,38,39,39,39,40,40,40,41,41,41,16,39,40,41,42,42,42,10,42,43,44,43,43,44,44,43,44,45,46,45,45,45,42,46,46,46,38,47,48,47,47,48,48,47,48,49,50,49,49,49,23,50,50,50,17,43,44,45,46,47,48,49,50,51,52,53,54,51,51,51,40,52,52,52,20,51,52,30,6,53,53,53,36,54,54,54,14,53,54,28,4,1,2,3,5,7,8,9,11,13,15,19,21,25,26,27,29,31,32,33,34,35,37,39,41,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,60,58,59,56,57,55,55,55,56,56,55,56,57,57,58,58,57,58,59,59,60,60,59,60,55,56,57,58,59,60]
lemma row0_0_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_0 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 4 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_0_0 q
  · exact row0_0_1 q
  · exact row0_0_2 q
  · exact row0_0_3 q
  · exact row0_0_4 q
lemma row0_1_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by decide +kernel
lemma row0_1 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 4 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) = (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_1_0 q
  · exact row0_1_1 q
  · exact row0_1_2 q
  · exact row0_1_3 q
  · exact row0_1_4 q
lemma row0_2_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by decide +kernel
lemma row0_2 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 4 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ())))))) = (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_2_0 q
  · exact row0_2_1 q
  · exact row0_2_2 q
  · exact row0_2_3 q
  · exact row0_2_4 q
lemma row0_3_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row0_3 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 4 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_3_0 q
  · exact row0_3_1 q
  · exact row0_3_2 q
  · exact row0_3_3 q
  · exact row0_3_4 q
lemma row0_4_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ())))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ())))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ())))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ())))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ())))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row0_4 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 4 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))) →
    enc0 (SixRows4.key0 (q,(Sum.inl (Sum.inr ())))) = (FiveRows2.key0 (smallOrder0 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_4_0 q
  · exact row0_4_1 q
  · exact row0_4_2 q
  · exact row0_4_3 q
  · exact row0_4_4 q
lemma row0_5_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ()))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ()))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ()))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ()))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inl (Sum.inr ()))),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 4 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))) →
    enc0 (SixRows4.key0 ((q,(Sum.inr ())),(Sum.inr ()))) = (FiveRows2.key0 (smallOrder0 ((q,(Sum.inr ())),(Sum.inr ())))).val + 1 := by decide +kernel
lemma row0_5 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 4 (smallOrder0 (q,(Sum.inr ())))).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 (q,(Sum.inr ())))) →
    enc0 (SixRows4.key0 (q,(Sum.inr ()))) = (FiveRows2.key0 (smallOrder0 (q,(Sum.inr ())))).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_5_0 q
  · exact row0_5_1 q
  · exact row0_5_2 q
  · exact row0_5_3 q
  · exact row0_5_4 q
lemma row0 : ∀ q : Marked.Order 5,
    (SmallOrderNormalization.normalized 4 (smallOrder0 q)).vertex =
      FiveRows2.words0 (FiveRows2.key0 (smallOrder0 q)) →
    enc0 (SixRows4.key0 q) = (FiveRows2.key0 (smallOrder0 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row0_0 q
  · exact row0_1 q
  · exact row0_2 q
  · exact row0_3 q
  · exact row0_4 q
  · exact row0_5 q

def enc1 : Fin 60 → ℕ := ![1,2,1,1,2,2,1,2,3,4,5,6,3,3,3,4,4,4,5,5,5,6,6,6,7,8,7,7,8,8,7,8,9,10,9,9,9,6,10,10,10,4,1,2,3,5,7,8,9,10,11,12,12,11,11,11,12,12,11,12]
lemma row1_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows2.words1 (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc1 (SixRows4.key1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows2.words1 (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc1 (SixRows4.key1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row1_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words1 (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc1 (SixRows4.key1 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row1_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words1 (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))) →
    enc1 (SixRows4.key1 (q,(Sum.inl (Sum.inr ())))) = (FiveRows2.key1 (smallOrder1 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row1_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder1 (q,(Sum.inr ())))).vertex =
      FiveRows2.words1 (FiveRows2.key1 (smallOrder1 (q,(Sum.inr ())))) →
    enc1 (SixRows4.key1 (q,(Sum.inr ()))) = (FiveRows2.key1 (smallOrder1 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row1 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder1 q)).vertex =
      FiveRows2.words1 (FiveRows2.key1 (smallOrder1 q)) →
    enc1 (SixRows4.key1 q) = (FiveRows2.key1 (smallOrder1 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row1_0 q
  · exact row1_1 q
  · exact row1_2 q
  · exact row1_3 q
  · exact row1_4 q

def enc2 : Fin 60 → ℕ := ![1,2,1,1,2,2,1,2,3,4,5,6,3,3,3,4,4,4,5,5,5,6,6,6,7,8,7,7,8,8,7,8,9,10,9,9,9,6,10,10,10,4,1,2,3,5,7,8,9,10,11,12,12,11,11,11,12,12,11,12]
lemma row2_0 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex =
      FiveRows2.words2 (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) →
    enc2 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))))) = (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).val + 1 := by decide +kernel
lemma row2_1 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).vertex =
      FiveRows2.words2 (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))) →
    enc2 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))))) = (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inl (1 : Fin 2))))))).val + 1 := by decide +kernel
lemma row2_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).vertex =
      FiveRows2.words2 (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inr ())))))) →
    enc2 (SixRows4.key2 (q,(Sum.inl (Sum.inl (Sum.inr ()))))) = (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inl (Sum.inr ())))))).val + 1 := by decide +kernel
lemma row2_3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inl (Sum.inr ()))))).vertex =
      FiveRows2.words2 (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inr ()))))) →
    enc2 (SixRows4.key2 (q,(Sum.inl (Sum.inr ())))) = (FiveRows2.key2 (smallOrder2 (q,(Sum.inl (Sum.inr ()))))).val + 1 := by decide +kernel
lemma row2_4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 3 (smallOrder2 (q,(Sum.inr ())))).vertex =
      FiveRows2.words2 (FiveRows2.key2 (smallOrder2 (q,(Sum.inr ())))) →
    enc2 (SixRows4.key2 (q,(Sum.inr ()))) = (FiveRows2.key2 (smallOrder2 (q,(Sum.inr ())))).val + 1 := by decide +kernel
lemma row2 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 3 (smallOrder2 q)).vertex =
      FiveRows2.words2 (FiveRows2.key2 (smallOrder2 q)) →
    enc2 (SixRows4.key2 q) = (FiveRows2.key2 (smallOrder2 q)).val + 1 := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact row2_0 q
  · exact row2_1 q
  · exact row2_2 q
  · exact row2_3 q
  · exact row2_4 q

def enc3 : Fin 12 → ℕ := ![1,1,1,2,2,2,3,3,3,2,1,3]
lemma row3 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder3 q)).vertex =
      FiveRows2.words3 (FiveRows2.key3 (smallOrder3 q)) →
    enc3 (SixRows4.key4 q) = (FiveRows2.key3 (smallOrder3 q)).val + 1 := by decide +kernel

def enc4 : Fin 12 → ℕ := ![1,1,1,2,2,2,3,3,3,2,1,3]
lemma row4 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 2 (smallOrder4 q)).vertex =
      FiveRows2.words4 (FiveRows2.key4 (smallOrder4 q)) →
    enc4 (SixRows4.key5 q) = (FiveRows2.key4 (smallOrder4 q)).val + 1 := by decide +kernel

def goodCodes : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(25,10,12,1,2),(25,10,12,2,2),(25,10,12,2,3),(26,9,11,2,1),(26,9,11,2,2),(26,9,11,3,2),(27,10,1,3,1),(27,10,1,3,3),(27,12,2,1,3),(27,12,2,3,3),(28,12,11,2,1),(28,12,11,2,2),(28,12,11,3,2),(29,9,2,1,3),(29,9,2,3,3),(29,11,1,3,1),(29,11,1,3,3),(30,11,12,1,2),(30,11,12,2,2),(30,11,12,2,3),(35,5,7,2,3),(35,5,7,3,2),(35,5,7,3,3),(35,8,3,1,1),(35,8,3,1,2),(35,8,3,2,1),(36,1,11,1,1),(36,1,11,1,3),(36,2,9,1,1),(36,2,9,3,1),(38,11,9,1,2),(38,11,9,2,2),(38,11,9,2,3),(39,3,8,2,3),(39,3,8,3,2),(39,3,8,3,3),(39,7,5,1,1),(39,7,5,1,2),(39,7,5,2,1),(40,1,10,1,1),(40,1,10,1,3),(40,2,12,1,1),(40,2,12,3,1),(42,12,10,2,1),(42,12,10,2,2),(42,12,10,3,2),(43,10,9,1,2),(43,10,9,2,2),(43,10,9,2,3),(44,9,10,2,1),(44,9,10,2,2),(44,9,10,3,2),(45,10,6,3,1),(45,10,6,3,3),(45,12,4,1,3),(45,12,4,3,3),(46,9,4,1,3),(46,9,4,3,3),(46,11,6,3,1),(46,11,6,3,3),(51,5,8,2,3),(51,5,8,3,2),(51,5,8,3,3),(51,8,5,1,1),(51,8,5,1,2),(51,8,5,2,1),(53,3,7,2,3),(53,3,7,3,2),(53,3,7,3,3),(53,7,3,1,1),(53,7,3,1,2),(53,7,3,2,1),(57,4,9,1,1),(57,4,9,3,1),(57,6,11,1,1),(57,6,11,1,3),(59,4,12,1,1),(59,4,12,3,1),(59,6,10,1,1),(59,6,10,1,3)}
def Compatible (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Prop :=
  (enc0 q0,enc1 q1,enc2 q2,enc3 q4,enc4 q5) ∈ goodCodes
instance (q0 : Fin 360) (q1 : Fin 60) (q2 : Fin 60) (q3 : Fin 12) (q4 : Fin 12) (q5 : Fin 12) : Decidable (Compatible q0 q1 q2 q3 q4 q5) :=
  inferInstanceAs (Decidable (_ ∈ goodCodes))

/- Direct catalogue insertion proofs avoid evaluating nested finset deduplication. -/
/- Factored catalogue insertion proofs avoid repeated long prefixes. -/
/- Opaque-index catalogue assembly; value equalities are checked separately. -/
def CodesValue (i : FiveWordOrbits2.Cases) : (ℕ × ℕ × ℕ × ℕ × ℕ) := ((FiveRows2.digit0 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit1 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit2 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit3 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit4 (FiveWordOrbits2.caseKey i).val).val + 1)
def CodesAt (i : FiveWordOrbits2.Cases) : Prop := CodesValue i ∈ goodCodes
def CodesIndex (j : ℕ) : Prop := ∀ hj : j < 80, CodesAt ⟨j,hj⟩
def codeSuffix00 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := goodCodes
lemma codeSuffix00_subset : codeSuffix00 ⊆ goodCodes := by
  intro x hx
  exact hx
def codeSuffix01 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(29,11,1,3,3),(30,11,12,1,2),(30,11,12,2,2),(30,11,12,2,3),(35,5,7,2,3),(35,5,7,3,2),(35,5,7,3,3),(35,8,3,1,1),(35,8,3,1,2),(35,8,3,2,1),(36,1,11,1,1),(36,1,11,1,3),(36,2,9,1,1),(36,2,9,3,1),(38,11,9,1,2),(38,11,9,2,2),(38,11,9,2,3),(39,3,8,2,3),(39,3,8,3,2),(39,3,8,3,3),(39,7,5,1,1),(39,7,5,1,2),(39,7,5,2,1),(40,1,10,1,1),(40,1,10,1,3),(40,2,12,1,1),(40,2,12,3,1),(42,12,10,2,1),(42,12,10,2,2),(42,12,10,3,2),(43,10,9,1,2),(43,10,9,2,2),(43,10,9,2,3),(44,9,10,2,1),(44,9,10,2,2),(44,9,10,3,2),(45,10,6,3,1),(45,10,6,3,3),(45,12,4,1,3),(45,12,4,3,3),(46,9,4,1,3),(46,9,4,3,3),(46,11,6,3,1),(46,11,6,3,3),(51,5,8,2,3),(51,5,8,3,2),(51,5,8,3,3),(51,8,5,1,1),(51,8,5,1,2),(51,8,5,2,1),(53,3,7,2,3),(53,3,7,3,2),(53,3,7,3,3),(53,7,3,1,1),(53,7,3,1,2),(53,7,3,2,1),(57,4,9,1,1),(57,4,9,3,1),(57,6,11,1,1),(57,6,11,1,3),(59,4,12,1,1),(59,4,12,3,1),(59,6,10,1,1),(59,6,10,1,3)}
lemma codeSuffix01_subset : codeSuffix01 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix01 at hx
  apply codeSuffix00_subset
  unfold codeSuffix00 goodCodes
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix02 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(38,11,9,2,3),(39,3,8,2,3),(39,3,8,3,2),(39,3,8,3,3),(39,7,5,1,1),(39,7,5,1,2),(39,7,5,2,1),(40,1,10,1,1),(40,1,10,1,3),(40,2,12,1,1),(40,2,12,3,1),(42,12,10,2,1),(42,12,10,2,2),(42,12,10,3,2),(43,10,9,1,2),(43,10,9,2,2),(43,10,9,2,3),(44,9,10,2,1),(44,9,10,2,2),(44,9,10,3,2),(45,10,6,3,1),(45,10,6,3,3),(45,12,4,1,3),(45,12,4,3,3),(46,9,4,1,3),(46,9,4,3,3),(46,11,6,3,1),(46,11,6,3,3),(51,5,8,2,3),(51,5,8,3,2),(51,5,8,3,3),(51,8,5,1,1),(51,8,5,1,2),(51,8,5,2,1),(53,3,7,2,3),(53,3,7,3,2),(53,3,7,3,3),(53,7,3,1,1),(53,7,3,1,2),(53,7,3,2,1),(57,4,9,1,1),(57,4,9,3,1),(57,6,11,1,1),(57,6,11,1,3),(59,4,12,1,1),(59,4,12,3,1),(59,6,10,1,1),(59,6,10,1,3)}
lemma codeSuffix02_subset : codeSuffix02 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix02 at hx
  apply codeSuffix01_subset
  unfold codeSuffix01
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix03 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(43,10,9,2,3),(44,9,10,2,1),(44,9,10,2,2),(44,9,10,3,2),(45,10,6,3,1),(45,10,6,3,3),(45,12,4,1,3),(45,12,4,3,3),(46,9,4,1,3),(46,9,4,3,3),(46,11,6,3,1),(46,11,6,3,3),(51,5,8,2,3),(51,5,8,3,2),(51,5,8,3,3),(51,8,5,1,1),(51,8,5,1,2),(51,8,5,2,1),(53,3,7,2,3),(53,3,7,3,2),(53,3,7,3,3),(53,7,3,1,1),(53,7,3,1,2),(53,7,3,2,1),(57,4,9,1,1),(57,4,9,3,1),(57,6,11,1,1),(57,6,11,1,3),(59,4,12,1,1),(59,4,12,3,1),(59,6,10,1,1),(59,6,10,1,3)}
lemma codeSuffix03_subset : codeSuffix03 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix03 at hx
  apply codeSuffix02_subset
  unfold codeSuffix02
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
def codeSuffix04 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {(51,8,5,1,2),(51,8,5,2,1),(53,3,7,2,3),(53,3,7,3,2),(53,3,7,3,3),(53,7,3,1,1),(53,7,3,1,2),(53,7,3,2,1),(57,4,9,1,1),(57,4,9,3,1),(57,6,11,1,1),(57,6,11,1,3),(59,4,12,1,1),(59,4,12,3,1),(59,6,10,1,1),(59,6,10,1,3)}
lemma codeSuffix04_subset : codeSuffix04 ⊆ goodCodes := by
  intro x hx
  unfold codeSuffix04 at hx
  apply codeSuffix03_subset
  unfold codeSuffix03
  iterate 16 apply Finset.mem_insert_of_mem
  exact hx
lemma codes_case0 : CodesAt 0 := by
  have hv : CodesValue 0 = (25,10,12,1,2) := by rfl
  have hm : (25,10,12,1,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case1 : CodesAt 1 := by
  have hv : CodesValue 1 = (25,10,12,2,2) := by rfl
  have hm : (25,10,12,2,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case2 : CodesAt 2 := by
  have hv : CodesValue 2 = (25,10,12,2,3) := by rfl
  have hm : (25,10,12,2,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case3 : CodesAt 3 := by
  have hv : CodesValue 3 = (26,9,11,2,1) := by rfl
  have hm : (26,9,11,2,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case4 : CodesAt 4 := by
  have hv : CodesValue 4 = (26,9,11,2,2) := by rfl
  have hm : (26,9,11,2,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case5 : CodesAt 5 := by
  have hv : CodesValue 5 = (26,9,11,3,2) := by rfl
  have hm : (26,9,11,3,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case6 : CodesAt 6 := by
  have hv : CodesValue 6 = (27,10,1,3,1) := by rfl
  have hm : (27,10,1,3,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case7 : CodesAt 7 := by
  have hv : CodesValue 7 = (27,10,1,3,3) := by rfl
  have hm : (27,10,1,3,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case8 : CodesAt 8 := by
  have hv : CodesValue 8 = (27,12,2,1,3) := by rfl
  have hm : (27,12,2,1,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case9 : CodesAt 9 := by
  have hv : CodesValue 9 = (27,12,2,3,3) := by rfl
  have hm : (27,12,2,3,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case10 : CodesAt 10 := by
  have hv : CodesValue 10 = (28,12,11,2,1) := by rfl
  have hm : (28,12,11,2,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case11 : CodesAt 11 := by
  have hv : CodesValue 11 = (28,12,11,2,2) := by rfl
  have hm : (28,12,11,2,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case12 : CodesAt 12 := by
  have hv : CodesValue 12 = (28,12,11,3,2) := by rfl
  have hm : (28,12,11,3,2) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case13 : CodesAt 13 := by
  have hv : CodesValue 13 = (29,9,2,1,3) := by rfl
  have hm : (29,9,2,1,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case14 : CodesAt 14 := by
  have hv : CodesValue 14 = (29,9,2,3,3) := by rfl
  have hm : (29,9,2,3,3) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case15 : CodesAt 15 := by
  have hv : CodesValue 15 = (29,11,1,3,1) := by rfl
  have hm : (29,11,1,3,1) ∈ codeSuffix00 := by
    unfold codeSuffix00 goodCodes
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix00_subset hm)
lemma codes_case16 : CodesAt 16 := by
  have hv : CodesValue 16 = (29,11,1,3,3) := by rfl
  have hm : (29,11,1,3,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case17 : CodesAt 17 := by
  have hv : CodesValue 17 = (30,11,12,1,2) := by rfl
  have hm : (30,11,12,1,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case18 : CodesAt 18 := by
  have hv : CodesValue 18 = (30,11,12,2,2) := by rfl
  have hm : (30,11,12,2,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case19 : CodesAt 19 := by
  have hv : CodesValue 19 = (30,11,12,2,3) := by rfl
  have hm : (30,11,12,2,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case20 : CodesAt 20 := by
  have hv : CodesValue 20 = (35,5,7,2,3) := by rfl
  have hm : (35,5,7,2,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case21 : CodesAt 21 := by
  have hv : CodesValue 21 = (35,5,7,3,2) := by rfl
  have hm : (35,5,7,3,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case22 : CodesAt 22 := by
  have hv : CodesValue 22 = (35,5,7,3,3) := by rfl
  have hm : (35,5,7,3,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case23 : CodesAt 23 := by
  have hv : CodesValue 23 = (35,8,3,1,1) := by rfl
  have hm : (35,8,3,1,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case24 : CodesAt 24 := by
  have hv : CodesValue 24 = (35,8,3,1,2) := by rfl
  have hm : (35,8,3,1,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case25 : CodesAt 25 := by
  have hv : CodesValue 25 = (35,8,3,2,1) := by rfl
  have hm : (35,8,3,2,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case26 : CodesAt 26 := by
  have hv : CodesValue 26 = (36,1,11,1,1) := by rfl
  have hm : (36,1,11,1,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case27 : CodesAt 27 := by
  have hv : CodesValue 27 = (36,1,11,1,3) := by rfl
  have hm : (36,1,11,1,3) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case28 : CodesAt 28 := by
  have hv : CodesValue 28 = (36,2,9,1,1) := by rfl
  have hm : (36,2,9,1,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case29 : CodesAt 29 := by
  have hv : CodesValue 29 = (36,2,9,3,1) := by rfl
  have hm : (36,2,9,3,1) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case30 : CodesAt 30 := by
  have hv : CodesValue 30 = (38,11,9,1,2) := by rfl
  have hm : (38,11,9,1,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case31 : CodesAt 31 := by
  have hv : CodesValue 31 = (38,11,9,2,2) := by rfl
  have hm : (38,11,9,2,2) ∈ codeSuffix01 := by
    unfold codeSuffix01
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix01_subset hm)
lemma codes_case32 : CodesAt 32 := by
  have hv : CodesValue 32 = (38,11,9,2,3) := by rfl
  have hm : (38,11,9,2,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case33 : CodesAt 33 := by
  have hv : CodesValue 33 = (39,3,8,2,3) := by rfl
  have hm : (39,3,8,2,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case34 : CodesAt 34 := by
  have hv : CodesValue 34 = (39,3,8,3,2) := by rfl
  have hm : (39,3,8,3,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case35 : CodesAt 35 := by
  have hv : CodesValue 35 = (39,3,8,3,3) := by rfl
  have hm : (39,3,8,3,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case36 : CodesAt 36 := by
  have hv : CodesValue 36 = (39,7,5,1,1) := by rfl
  have hm : (39,7,5,1,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case37 : CodesAt 37 := by
  have hv : CodesValue 37 = (39,7,5,1,2) := by rfl
  have hm : (39,7,5,1,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case38 : CodesAt 38 := by
  have hv : CodesValue 38 = (39,7,5,2,1) := by rfl
  have hm : (39,7,5,2,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case39 : CodesAt 39 := by
  have hv : CodesValue 39 = (40,1,10,1,1) := by rfl
  have hm : (40,1,10,1,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case40 : CodesAt 40 := by
  have hv : CodesValue 40 = (40,1,10,1,3) := by rfl
  have hm : (40,1,10,1,3) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case41 : CodesAt 41 := by
  have hv : CodesValue 41 = (40,2,12,1,1) := by rfl
  have hm : (40,2,12,1,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case42 : CodesAt 42 := by
  have hv : CodesValue 42 = (40,2,12,3,1) := by rfl
  have hm : (40,2,12,3,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case43 : CodesAt 43 := by
  have hv : CodesValue 43 = (42,12,10,2,1) := by rfl
  have hm : (42,12,10,2,1) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case44 : CodesAt 44 := by
  have hv : CodesValue 44 = (42,12,10,2,2) := by rfl
  have hm : (42,12,10,2,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case45 : CodesAt 45 := by
  have hv : CodesValue 45 = (42,12,10,3,2) := by rfl
  have hm : (42,12,10,3,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case46 : CodesAt 46 := by
  have hv : CodesValue 46 = (43,10,9,1,2) := by rfl
  have hm : (43,10,9,1,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case47 : CodesAt 47 := by
  have hv : CodesValue 47 = (43,10,9,2,2) := by rfl
  have hm : (43,10,9,2,2) ∈ codeSuffix02 := by
    unfold codeSuffix02
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix02_subset hm)
lemma codes_case48 : CodesAt 48 := by
  have hv : CodesValue 48 = (43,10,9,2,3) := by rfl
  have hm : (43,10,9,2,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case49 : CodesAt 49 := by
  have hv : CodesValue 49 = (44,9,10,2,1) := by rfl
  have hm : (44,9,10,2,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case50 : CodesAt 50 := by
  have hv : CodesValue 50 = (44,9,10,2,2) := by rfl
  have hm : (44,9,10,2,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case51 : CodesAt 51 := by
  have hv : CodesValue 51 = (44,9,10,3,2) := by rfl
  have hm : (44,9,10,3,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case52 : CodesAt 52 := by
  have hv : CodesValue 52 = (45,10,6,3,1) := by rfl
  have hm : (45,10,6,3,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case53 : CodesAt 53 := by
  have hv : CodesValue 53 = (45,10,6,3,3) := by rfl
  have hm : (45,10,6,3,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case54 : CodesAt 54 := by
  have hv : CodesValue 54 = (45,12,4,1,3) := by rfl
  have hm : (45,12,4,1,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case55 : CodesAt 55 := by
  have hv : CodesValue 55 = (45,12,4,3,3) := by rfl
  have hm : (45,12,4,3,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case56 : CodesAt 56 := by
  have hv : CodesValue 56 = (46,9,4,1,3) := by rfl
  have hm : (46,9,4,1,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case57 : CodesAt 57 := by
  have hv : CodesValue 57 = (46,9,4,3,3) := by rfl
  have hm : (46,9,4,3,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case58 : CodesAt 58 := by
  have hv : CodesValue 58 = (46,11,6,3,1) := by rfl
  have hm : (46,11,6,3,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case59 : CodesAt 59 := by
  have hv : CodesValue 59 = (46,11,6,3,3) := by rfl
  have hm : (46,11,6,3,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case60 : CodesAt 60 := by
  have hv : CodesValue 60 = (51,5,8,2,3) := by rfl
  have hm : (51,5,8,2,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case61 : CodesAt 61 := by
  have hv : CodesValue 61 = (51,5,8,3,2) := by rfl
  have hm : (51,5,8,3,2) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case62 : CodesAt 62 := by
  have hv : CodesValue 62 = (51,5,8,3,3) := by rfl
  have hm : (51,5,8,3,3) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case63 : CodesAt 63 := by
  have hv : CodesValue 63 = (51,8,5,1,1) := by rfl
  have hm : (51,8,5,1,1) ∈ codeSuffix03 := by
    unfold codeSuffix03
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix03_subset hm)
lemma codes_case64 : CodesAt 64 := by
  have hv : CodesValue 64 = (51,8,5,1,2) := by rfl
  have hm : (51,8,5,1,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case65 : CodesAt 65 := by
  have hv : CodesValue 65 = (51,8,5,2,1) := by rfl
  have hm : (51,8,5,2,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 1 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case66 : CodesAt 66 := by
  have hv : CodesValue 66 = (53,3,7,2,3) := by rfl
  have hm : (53,3,7,2,3) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 2 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case67 : CodesAt 67 := by
  have hv : CodesValue 67 = (53,3,7,3,2) := by rfl
  have hm : (53,3,7,3,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 3 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case68 : CodesAt 68 := by
  have hv : CodesValue 68 = (53,3,7,3,3) := by rfl
  have hm : (53,3,7,3,3) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 4 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case69 : CodesAt 69 := by
  have hv : CodesValue 69 = (53,7,3,1,1) := by rfl
  have hm : (53,7,3,1,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 5 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case70 : CodesAt 70 := by
  have hv : CodesValue 70 = (53,7,3,1,2) := by rfl
  have hm : (53,7,3,1,2) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 6 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case71 : CodesAt 71 := by
  have hv : CodesValue 71 = (53,7,3,2,1) := by rfl
  have hm : (53,7,3,2,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 7 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case72 : CodesAt 72 := by
  have hv : CodesValue 72 = (57,4,9,1,1) := by rfl
  have hm : (57,4,9,1,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 8 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case73 : CodesAt 73 := by
  have hv : CodesValue 73 = (57,4,9,3,1) := by rfl
  have hm : (57,4,9,3,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 9 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case74 : CodesAt 74 := by
  have hv : CodesValue 74 = (57,6,11,1,1) := by rfl
  have hm : (57,6,11,1,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 10 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case75 : CodesAt 75 := by
  have hv : CodesValue 75 = (57,6,11,1,3) := by rfl
  have hm : (57,6,11,1,3) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 11 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case76 : CodesAt 76 := by
  have hv : CodesValue 76 = (59,4,12,1,1) := by rfl
  have hm : (59,4,12,1,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 12 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case77 : CodesAt 77 := by
  have hv : CodesValue 77 = (59,4,12,3,1) := by rfl
  have hm : (59,4,12,3,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 13 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case78 : CodesAt 78 := by
  have hv : CodesValue 78 = (59,6,10,1,1) := by rfl
  have hm : (59,6,10,1,1) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 14 apply Finset.mem_insert_of_mem
    exact Finset.mem_insert_self _ _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_case79 : CodesAt 79 := by
  have hv : CodesValue 79 = (59,6,10,1,3) := by rfl
  have hm : (59,6,10,1,3) ∈ codeSuffix04 := by
    unfold codeSuffix04
    iterate 15 apply Finset.mem_insert_of_mem
    exact Finset.mem_singleton_self _
  exact Eq.mp (congrArg (fun x : (ℕ × ℕ × ℕ × ℕ × ℕ) => x ∈ goodCodes) hv.symm) (codeSuffix04_subset hm)
lemma codes_interval00 : FiniteIntervals.Covers CodesIndex 0 16 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 0 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case0
  · intro hj
    exact codes_case1
  · intro hj
    exact codes_case2
  · intro hj
    exact codes_case3
  · intro hj
    exact codes_case4
  · intro hj
    exact codes_case5
  · intro hj
    exact codes_case6
  · intro hj
    exact codes_case7
  · intro hj
    exact codes_case8
  · intro hj
    exact codes_case9
  · intro hj
    exact codes_case10
  · intro hj
    exact codes_case11
  · intro hj
    exact codes_case12
  · intro hj
    exact codes_case13
  · intro hj
    exact codes_case14
  · intro hj
    exact codes_case15
lemma codes_interval01 : FiniteIntervals.Covers CodesIndex 16 32 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 16 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case16
  · intro hj
    exact codes_case17
  · intro hj
    exact codes_case18
  · intro hj
    exact codes_case19
  · intro hj
    exact codes_case20
  · intro hj
    exact codes_case21
  · intro hj
    exact codes_case22
  · intro hj
    exact codes_case23
  · intro hj
    exact codes_case24
  · intro hj
    exact codes_case25
  · intro hj
    exact codes_case26
  · intro hj
    exact codes_case27
  · intro hj
    exact codes_case28
  · intro hj
    exact codes_case29
  · intro hj
    exact codes_case30
  · intro hj
    exact codes_case31
lemma codes_interval02 : FiniteIntervals.Covers CodesIndex 32 48 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 32 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case32
  · intro hj
    exact codes_case33
  · intro hj
    exact codes_case34
  · intro hj
    exact codes_case35
  · intro hj
    exact codes_case36
  · intro hj
    exact codes_case37
  · intro hj
    exact codes_case38
  · intro hj
    exact codes_case39
  · intro hj
    exact codes_case40
  · intro hj
    exact codes_case41
  · intro hj
    exact codes_case42
  · intro hj
    exact codes_case43
  · intro hj
    exact codes_case44
  · intro hj
    exact codes_case45
  · intro hj
    exact codes_case46
  · intro hj
    exact codes_case47
lemma codes_interval03 : FiniteIntervals.Covers CodesIndex 48 64 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 48 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case48
  · intro hj
    exact codes_case49
  · intro hj
    exact codes_case50
  · intro hj
    exact codes_case51
  · intro hj
    exact codes_case52
  · intro hj
    exact codes_case53
  · intro hj
    exact codes_case54
  · intro hj
    exact codes_case55
  · intro hj
    exact codes_case56
  · intro hj
    exact codes_case57
  · intro hj
    exact codes_case58
  · intro hj
    exact codes_case59
  · intro hj
    exact codes_case60
  · intro hj
    exact codes_case61
  · intro hj
    exact codes_case62
  · intro hj
    exact codes_case63
lemma codes_interval04 : FiniteIntervals.Covers CodesIndex 64 80 := by
  apply FiniteIntervals.of_fin (P := CodesIndex) 64 16
  intro i
  fin_cases i
  · intro hj
    exact codes_case64
  · intro hj
    exact codes_case65
  · intro hj
    exact codes_case66
  · intro hj
    exact codes_case67
  · intro hj
    exact codes_case68
  · intro hj
    exact codes_case69
  · intro hj
    exact codes_case70
  · intro hj
    exact codes_case71
  · intro hj
    exact codes_case72
  · intro hj
    exact codes_case73
  · intro hj
    exact codes_case74
  · intro hj
    exact codes_case75
  · intro hj
    exact codes_case76
  · intro hj
    exact codes_case77
  · intro hj
    exact codes_case78
  · intro hj
    exact codes_case79
lemma codes_valid : ∀ i : FiveWordOrbits2.Cases, ((FiveRows2.digit0 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit1 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit2 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit3 (FiveWordOrbits2.caseKey i).val).val + 1,(FiveRows2.digit4 (FiveWordOrbits2.caseKey i).val).val + 1) ∈ goodCodes := by
  intro i
  have hc : FiniteIntervals.Covers CodesIndex 0 80 := (FiniteIntervals.merge (FiniteIntervals.merge codes_interval00 codes_interval01) (FiniteIntervals.merge codes_interval02 (FiniteIntervals.merge codes_interval03 codes_interval04)))
  exact hc i.val (Nat.zero_le _) i.isLt i.isLt
lemma codes_of_good (j : Fin 77760) (hj : j ∈ FiveRows2.good) :
    ((FiveRows2.digit0 j.val).val + 1,(FiveRows2.digit1 j.val).val + 1,(FiveRows2.digit2 j.val).val + 1,(FiveRows2.digit3 j.val).val + 1,(FiveRows2.digit4 j.val).val + 1) ∈ goodCodes := by
  rw [FiveWordOrbits2.good_eq] at hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact codes_valid i

lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    Compatible (SixRows4.key0 (o 0)) (SixRows4.key1 (o 1)) (SixRows4.key2 (o 2)) (SixRows4.key3 (o 3)) (SixRows4.key4 (o 4)) (SixRows4.key5 (o 5)) := by
  have hs := SixProjection43.localBounds o h
  have hc := codes_of_good ⟨FiveRows2.key (smallOrders o),FiveRows2.key_lt (smallOrders o)⟩
    (SixProjection43.catalogue o h)
  rw [FiveRows2.digit_key0,FiveRows2.digit_key1,FiveRows2.digit_key2,FiveRows2.digit_key3,FiveRows2.digit_key4] at hc
  have hr0 := FiveRows2.chosen0 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr0
  have he0 := row0 (o 0) hr0
  have hr1 := FiveRows2.chosen1 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr1
  have he1 := row1 (o 1) hr1
  have hr2 := FiveRows2.chosen2 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr2
  have he2 := row2 (o 2) hr2
  have hr3 := FiveRows2.chosen3 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr3
  have he3 := row3 (o 4) hr3
  have hr4 := FiveRows2.chosen4 (smallOrders o) hs
  simp only [smallOrders,Fin.cases_zero,Fin.cases_succ] at hr4
  have he4 := row4 (o 5) hr4
  unfold Compatible
  rw [he0,he1,he2,he3,he4]
  simpa only [smallOrders,Fin.cases_zero,Fin.cases_succ] using hc

#print axioms compatible
end Erdos184Work.SixProjectionCode43
