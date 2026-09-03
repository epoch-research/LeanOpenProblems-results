import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub29_0 : ∀ i : Fin 1, ValidAt (348 + i.val) := by decide +kernel
lemma valid_part29_0 : FiniteIntervals.Covers ValidAt 348 349 :=
  FiniteIntervals.of_fin 348 1 valid_sub29_0
lemma valid_sub29_1 : ∀ i : Fin 1, ValidAt (349 + i.val) := by decide +kernel
lemma valid_part29_1 : FiniteIntervals.Covers ValidAt 349 350 :=
  FiniteIntervals.of_fin 349 1 valid_sub29_1
lemma valid_sub29_2 : ∀ i : Fin 1, ValidAt (350 + i.val) := by decide +kernel
lemma valid_part29_2 : FiniteIntervals.Covers ValidAt 350 351 :=
  FiniteIntervals.of_fin 350 1 valid_sub29_2
lemma valid_sub29_3 : ∀ i : Fin 1, ValidAt (351 + i.val) := by decide +kernel
lemma valid_part29_3 : FiniteIntervals.Covers ValidAt 351 352 :=
  FiniteIntervals.of_fin 351 1 valid_sub29_3
lemma valid_sub29_4 : ∀ i : Fin 1, ValidAt (352 + i.val) := by decide +kernel
lemma valid_part29_4 : FiniteIntervals.Covers ValidAt 352 353 :=
  FiniteIntervals.of_fin 352 1 valid_sub29_4
lemma valid_sub29_5 : ∀ i : Fin 1, ValidAt (353 + i.val) := by decide +kernel
lemma valid_part29_5 : FiniteIntervals.Covers ValidAt 353 354 :=
  FiniteIntervals.of_fin 353 1 valid_sub29_5
lemma valid_sub29_6 : ∀ i : Fin 1, ValidAt (354 + i.val) := by decide +kernel
lemma valid_part29_6 : FiniteIntervals.Covers ValidAt 354 355 :=
  FiniteIntervals.of_fin 354 1 valid_sub29_6
lemma valid_sub29_7 : ∀ i : Fin 1, ValidAt (355 + i.val) := by decide +kernel
lemma valid_part29_7 : FiniteIntervals.Covers ValidAt 355 356 :=
  FiniteIntervals.of_fin 355 1 valid_sub29_7
lemma valid_sub29_8 : ∀ i : Fin 1, ValidAt (356 + i.val) := by decide +kernel
lemma valid_part29_8 : FiniteIntervals.Covers ValidAt 356 357 :=
  FiniteIntervals.of_fin 356 1 valid_sub29_8
lemma valid_sub29_9 : ∀ i : Fin 1, ValidAt (357 + i.val) := by decide +kernel
lemma valid_part29_9 : FiniteIntervals.Covers ValidAt 357 358 :=
  FiniteIntervals.of_fin 357 1 valid_sub29_9
lemma valid_sub29_10 : ∀ i : Fin 1, ValidAt (358 + i.val) := by decide +kernel
lemma valid_part29_10 : FiniteIntervals.Covers ValidAt 358 359 :=
  FiniteIntervals.of_fin 358 1 valid_sub29_10
lemma valid_sub29_11 : ∀ i : Fin 1, ValidAt (359 + i.val) := by decide +kernel
lemma valid_part29_11 : FiniteIntervals.Covers ValidAt 359 360 :=
  FiniteIntervals.of_fin 359 1 valid_sub29_11
lemma valid_interval29 : FiniteIntervals.Covers ValidAt 348 360 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part29_0 (FiniteIntervals.merge valid_part29_1 valid_part29_2)) (FiniteIntervals.merge valid_part29_3 (FiniteIntervals.merge valid_part29_4 valid_part29_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part29_6 (FiniteIntervals.merge valid_part29_7 valid_part29_8)) (FiniteIntervals.merge valid_part29_9 (FiniteIntervals.merge valid_part29_10 valid_part29_11))))
#print axioms valid_interval29
end Erdos184Work.PureSixActions0
