import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub31_0 : ∀ i : Fin 1, ValidAt (372 + i.val) := by decide +kernel
lemma valid_part31_0 : FiniteIntervals.Covers ValidAt 372 373 :=
  FiniteIntervals.of_fin 372 1 valid_sub31_0
lemma valid_sub31_1 : ∀ i : Fin 1, ValidAt (373 + i.val) := by decide +kernel
lemma valid_part31_1 : FiniteIntervals.Covers ValidAt 373 374 :=
  FiniteIntervals.of_fin 373 1 valid_sub31_1
lemma valid_sub31_2 : ∀ i : Fin 1, ValidAt (374 + i.val) := by decide +kernel
lemma valid_part31_2 : FiniteIntervals.Covers ValidAt 374 375 :=
  FiniteIntervals.of_fin 374 1 valid_sub31_2
lemma valid_sub31_3 : ∀ i : Fin 1, ValidAt (375 + i.val) := by decide +kernel
lemma valid_part31_3 : FiniteIntervals.Covers ValidAt 375 376 :=
  FiniteIntervals.of_fin 375 1 valid_sub31_3
lemma valid_sub31_4 : ∀ i : Fin 1, ValidAt (376 + i.val) := by decide +kernel
lemma valid_part31_4 : FiniteIntervals.Covers ValidAt 376 377 :=
  FiniteIntervals.of_fin 376 1 valid_sub31_4
lemma valid_sub31_5 : ∀ i : Fin 1, ValidAt (377 + i.val) := by decide +kernel
lemma valid_part31_5 : FiniteIntervals.Covers ValidAt 377 378 :=
  FiniteIntervals.of_fin 377 1 valid_sub31_5
lemma valid_sub31_6 : ∀ i : Fin 1, ValidAt (378 + i.val) := by decide +kernel
lemma valid_part31_6 : FiniteIntervals.Covers ValidAt 378 379 :=
  FiniteIntervals.of_fin 378 1 valid_sub31_6
lemma valid_sub31_7 : ∀ i : Fin 1, ValidAt (379 + i.val) := by decide +kernel
lemma valid_part31_7 : FiniteIntervals.Covers ValidAt 379 380 :=
  FiniteIntervals.of_fin 379 1 valid_sub31_7
lemma valid_sub31_8 : ∀ i : Fin 1, ValidAt (380 + i.val) := by decide +kernel
lemma valid_part31_8 : FiniteIntervals.Covers ValidAt 380 381 :=
  FiniteIntervals.of_fin 380 1 valid_sub31_8
lemma valid_sub31_9 : ∀ i : Fin 1, ValidAt (381 + i.val) := by decide +kernel
lemma valid_part31_9 : FiniteIntervals.Covers ValidAt 381 382 :=
  FiniteIntervals.of_fin 381 1 valid_sub31_9
lemma valid_sub31_10 : ∀ i : Fin 1, ValidAt (382 + i.val) := by decide +kernel
lemma valid_part31_10 : FiniteIntervals.Covers ValidAt 382 383 :=
  FiniteIntervals.of_fin 382 1 valid_sub31_10
lemma valid_sub31_11 : ∀ i : Fin 1, ValidAt (383 + i.val) := by decide +kernel
lemma valid_part31_11 : FiniteIntervals.Covers ValidAt 383 384 :=
  FiniteIntervals.of_fin 383 1 valid_sub31_11
lemma valid_interval31 : FiniteIntervals.Covers ValidAt 372 384 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part31_0 (FiniteIntervals.merge valid_part31_1 valid_part31_2)) (FiniteIntervals.merge valid_part31_3 (FiniteIntervals.merge valid_part31_4 valid_part31_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part31_6 (FiniteIntervals.merge valid_part31_7 valid_part31_8)) (FiniteIntervals.merge valid_part31_9 (FiniteIntervals.merge valid_part31_10 valid_part31_11))))
#print axioms valid_interval31
end Erdos184Work.PureSixActions0
