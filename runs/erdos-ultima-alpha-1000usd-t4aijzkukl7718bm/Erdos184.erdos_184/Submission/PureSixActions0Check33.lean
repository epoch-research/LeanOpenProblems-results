import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub33_0 : ∀ i : Fin 1, ValidAt (396 + i.val) := by decide +kernel
lemma valid_part33_0 : FiniteIntervals.Covers ValidAt 396 397 :=
  FiniteIntervals.of_fin 396 1 valid_sub33_0
lemma valid_sub33_1 : ∀ i : Fin 1, ValidAt (397 + i.val) := by decide +kernel
lemma valid_part33_1 : FiniteIntervals.Covers ValidAt 397 398 :=
  FiniteIntervals.of_fin 397 1 valid_sub33_1
lemma valid_sub33_2 : ∀ i : Fin 1, ValidAt (398 + i.val) := by decide +kernel
lemma valid_part33_2 : FiniteIntervals.Covers ValidAt 398 399 :=
  FiniteIntervals.of_fin 398 1 valid_sub33_2
lemma valid_sub33_3 : ∀ i : Fin 1, ValidAt (399 + i.val) := by decide +kernel
lemma valid_part33_3 : FiniteIntervals.Covers ValidAt 399 400 :=
  FiniteIntervals.of_fin 399 1 valid_sub33_3
lemma valid_sub33_4 : ∀ i : Fin 1, ValidAt (400 + i.val) := by decide +kernel
lemma valid_part33_4 : FiniteIntervals.Covers ValidAt 400 401 :=
  FiniteIntervals.of_fin 400 1 valid_sub33_4
lemma valid_sub33_5 : ∀ i : Fin 1, ValidAt (401 + i.val) := by decide +kernel
lemma valid_part33_5 : FiniteIntervals.Covers ValidAt 401 402 :=
  FiniteIntervals.of_fin 401 1 valid_sub33_5
lemma valid_sub33_6 : ∀ i : Fin 1, ValidAt (402 + i.val) := by decide +kernel
lemma valid_part33_6 : FiniteIntervals.Covers ValidAt 402 403 :=
  FiniteIntervals.of_fin 402 1 valid_sub33_6
lemma valid_sub33_7 : ∀ i : Fin 1, ValidAt (403 + i.val) := by decide +kernel
lemma valid_part33_7 : FiniteIntervals.Covers ValidAt 403 404 :=
  FiniteIntervals.of_fin 403 1 valid_sub33_7
lemma valid_sub33_8 : ∀ i : Fin 1, ValidAt (404 + i.val) := by decide +kernel
lemma valid_part33_8 : FiniteIntervals.Covers ValidAt 404 405 :=
  FiniteIntervals.of_fin 404 1 valid_sub33_8
lemma valid_sub33_9 : ∀ i : Fin 1, ValidAt (405 + i.val) := by decide +kernel
lemma valid_part33_9 : FiniteIntervals.Covers ValidAt 405 406 :=
  FiniteIntervals.of_fin 405 1 valid_sub33_9
lemma valid_sub33_10 : ∀ i : Fin 1, ValidAt (406 + i.val) := by decide +kernel
lemma valid_part33_10 : FiniteIntervals.Covers ValidAt 406 407 :=
  FiniteIntervals.of_fin 406 1 valid_sub33_10
lemma valid_sub33_11 : ∀ i : Fin 1, ValidAt (407 + i.val) := by decide +kernel
lemma valid_part33_11 : FiniteIntervals.Covers ValidAt 407 408 :=
  FiniteIntervals.of_fin 407 1 valid_sub33_11
lemma valid_interval33 : FiniteIntervals.Covers ValidAt 396 408 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part33_0 (FiniteIntervals.merge valid_part33_1 valid_part33_2)) (FiniteIntervals.merge valid_part33_3 (FiniteIntervals.merge valid_part33_4 valid_part33_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part33_6 (FiniteIntervals.merge valid_part33_7 valid_part33_8)) (FiniteIntervals.merge valid_part33_9 (FiniteIntervals.merge valid_part33_10 valid_part33_11))))
#print axioms valid_interval33
end Erdos184Work.PureSixActions0
