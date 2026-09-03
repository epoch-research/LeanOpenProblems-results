import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub30_0 : ∀ i : Fin 1, ValidAt (360 + i.val) := by decide +kernel
lemma valid_part30_0 : FiniteIntervals.Covers ValidAt 360 361 :=
  FiniteIntervals.of_fin 360 1 valid_sub30_0
lemma valid_sub30_1 : ∀ i : Fin 1, ValidAt (361 + i.val) := by decide +kernel
lemma valid_part30_1 : FiniteIntervals.Covers ValidAt 361 362 :=
  FiniteIntervals.of_fin 361 1 valid_sub30_1
lemma valid_sub30_2 : ∀ i : Fin 1, ValidAt (362 + i.val) := by decide +kernel
lemma valid_part30_2 : FiniteIntervals.Covers ValidAt 362 363 :=
  FiniteIntervals.of_fin 362 1 valid_sub30_2
lemma valid_sub30_3 : ∀ i : Fin 1, ValidAt (363 + i.val) := by decide +kernel
lemma valid_part30_3 : FiniteIntervals.Covers ValidAt 363 364 :=
  FiniteIntervals.of_fin 363 1 valid_sub30_3
lemma valid_sub30_4 : ∀ i : Fin 1, ValidAt (364 + i.val) := by decide +kernel
lemma valid_part30_4 : FiniteIntervals.Covers ValidAt 364 365 :=
  FiniteIntervals.of_fin 364 1 valid_sub30_4
lemma valid_sub30_5 : ∀ i : Fin 1, ValidAt (365 + i.val) := by decide +kernel
lemma valid_part30_5 : FiniteIntervals.Covers ValidAt 365 366 :=
  FiniteIntervals.of_fin 365 1 valid_sub30_5
lemma valid_sub30_6 : ∀ i : Fin 1, ValidAt (366 + i.val) := by decide +kernel
lemma valid_part30_6 : FiniteIntervals.Covers ValidAt 366 367 :=
  FiniteIntervals.of_fin 366 1 valid_sub30_6
lemma valid_sub30_7 : ∀ i : Fin 1, ValidAt (367 + i.val) := by decide +kernel
lemma valid_part30_7 : FiniteIntervals.Covers ValidAt 367 368 :=
  FiniteIntervals.of_fin 367 1 valid_sub30_7
lemma valid_sub30_8 : ∀ i : Fin 1, ValidAt (368 + i.val) := by decide +kernel
lemma valid_part30_8 : FiniteIntervals.Covers ValidAt 368 369 :=
  FiniteIntervals.of_fin 368 1 valid_sub30_8
lemma valid_sub30_9 : ∀ i : Fin 1, ValidAt (369 + i.val) := by decide +kernel
lemma valid_part30_9 : FiniteIntervals.Covers ValidAt 369 370 :=
  FiniteIntervals.of_fin 369 1 valid_sub30_9
lemma valid_sub30_10 : ∀ i : Fin 1, ValidAt (370 + i.val) := by decide +kernel
lemma valid_part30_10 : FiniteIntervals.Covers ValidAt 370 371 :=
  FiniteIntervals.of_fin 370 1 valid_sub30_10
lemma valid_sub30_11 : ∀ i : Fin 1, ValidAt (371 + i.val) := by decide +kernel
lemma valid_part30_11 : FiniteIntervals.Covers ValidAt 371 372 :=
  FiniteIntervals.of_fin 371 1 valid_sub30_11
lemma valid_interval30 : FiniteIntervals.Covers ValidAt 360 372 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part30_0 (FiniteIntervals.merge valid_part30_1 valid_part30_2)) (FiniteIntervals.merge valid_part30_3 (FiniteIntervals.merge valid_part30_4 valid_part30_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part30_6 (FiniteIntervals.merge valid_part30_7 valid_part30_8)) (FiniteIntervals.merge valid_part30_9 (FiniteIntervals.merge valid_part30_10 valid_part30_11))))
#print axioms valid_interval30
end Erdos184Work.PureSixActions0
