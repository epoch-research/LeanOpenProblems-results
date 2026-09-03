import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub24_0 : ∀ i : Fin 1, ValidAt (288 + i.val) := by decide +kernel
lemma valid_part24_0 : FiniteIntervals.Covers ValidAt 288 289 :=
  FiniteIntervals.of_fin 288 1 valid_sub24_0
lemma valid_sub24_1 : ∀ i : Fin 1, ValidAt (289 + i.val) := by decide +kernel
lemma valid_part24_1 : FiniteIntervals.Covers ValidAt 289 290 :=
  FiniteIntervals.of_fin 289 1 valid_sub24_1
lemma valid_sub24_2 : ∀ i : Fin 1, ValidAt (290 + i.val) := by decide +kernel
lemma valid_part24_2 : FiniteIntervals.Covers ValidAt 290 291 :=
  FiniteIntervals.of_fin 290 1 valid_sub24_2
lemma valid_sub24_3 : ∀ i : Fin 1, ValidAt (291 + i.val) := by decide +kernel
lemma valid_part24_3 : FiniteIntervals.Covers ValidAt 291 292 :=
  FiniteIntervals.of_fin 291 1 valid_sub24_3
lemma valid_sub24_4 : ∀ i : Fin 1, ValidAt (292 + i.val) := by decide +kernel
lemma valid_part24_4 : FiniteIntervals.Covers ValidAt 292 293 :=
  FiniteIntervals.of_fin 292 1 valid_sub24_4
lemma valid_sub24_5 : ∀ i : Fin 1, ValidAt (293 + i.val) := by decide +kernel
lemma valid_part24_5 : FiniteIntervals.Covers ValidAt 293 294 :=
  FiniteIntervals.of_fin 293 1 valid_sub24_5
lemma valid_sub24_6 : ∀ i : Fin 1, ValidAt (294 + i.val) := by decide +kernel
lemma valid_part24_6 : FiniteIntervals.Covers ValidAt 294 295 :=
  FiniteIntervals.of_fin 294 1 valid_sub24_6
lemma valid_sub24_7 : ∀ i : Fin 1, ValidAt (295 + i.val) := by decide +kernel
lemma valid_part24_7 : FiniteIntervals.Covers ValidAt 295 296 :=
  FiniteIntervals.of_fin 295 1 valid_sub24_7
lemma valid_sub24_8 : ∀ i : Fin 1, ValidAt (296 + i.val) := by decide +kernel
lemma valid_part24_8 : FiniteIntervals.Covers ValidAt 296 297 :=
  FiniteIntervals.of_fin 296 1 valid_sub24_8
lemma valid_sub24_9 : ∀ i : Fin 1, ValidAt (297 + i.val) := by decide +kernel
lemma valid_part24_9 : FiniteIntervals.Covers ValidAt 297 298 :=
  FiniteIntervals.of_fin 297 1 valid_sub24_9
lemma valid_sub24_10 : ∀ i : Fin 1, ValidAt (298 + i.val) := by decide +kernel
lemma valid_part24_10 : FiniteIntervals.Covers ValidAt 298 299 :=
  FiniteIntervals.of_fin 298 1 valid_sub24_10
lemma valid_sub24_11 : ∀ i : Fin 1, ValidAt (299 + i.val) := by decide +kernel
lemma valid_part24_11 : FiniteIntervals.Covers ValidAt 299 300 :=
  FiniteIntervals.of_fin 299 1 valid_sub24_11
lemma valid_interval24 : FiniteIntervals.Covers ValidAt 288 300 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part24_0 (FiniteIntervals.merge valid_part24_1 valid_part24_2)) (FiniteIntervals.merge valid_part24_3 (FiniteIntervals.merge valid_part24_4 valid_part24_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part24_6 (FiniteIntervals.merge valid_part24_7 valid_part24_8)) (FiniteIntervals.merge valid_part24_9 (FiniteIntervals.merge valid_part24_10 valid_part24_11))))
#print axioms valid_interval24
end Erdos184Work.PureSixActions0
