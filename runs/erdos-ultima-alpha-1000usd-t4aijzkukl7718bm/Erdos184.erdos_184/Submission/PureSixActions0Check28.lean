import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub28_0 : ∀ i : Fin 1, ValidAt (336 + i.val) := by decide +kernel
lemma valid_part28_0 : FiniteIntervals.Covers ValidAt 336 337 :=
  FiniteIntervals.of_fin 336 1 valid_sub28_0
lemma valid_sub28_1 : ∀ i : Fin 1, ValidAt (337 + i.val) := by decide +kernel
lemma valid_part28_1 : FiniteIntervals.Covers ValidAt 337 338 :=
  FiniteIntervals.of_fin 337 1 valid_sub28_1
lemma valid_sub28_2 : ∀ i : Fin 1, ValidAt (338 + i.val) := by decide +kernel
lemma valid_part28_2 : FiniteIntervals.Covers ValidAt 338 339 :=
  FiniteIntervals.of_fin 338 1 valid_sub28_2
lemma valid_sub28_3 : ∀ i : Fin 1, ValidAt (339 + i.val) := by decide +kernel
lemma valid_part28_3 : FiniteIntervals.Covers ValidAt 339 340 :=
  FiniteIntervals.of_fin 339 1 valid_sub28_3
lemma valid_sub28_4 : ∀ i : Fin 1, ValidAt (340 + i.val) := by decide +kernel
lemma valid_part28_4 : FiniteIntervals.Covers ValidAt 340 341 :=
  FiniteIntervals.of_fin 340 1 valid_sub28_4
lemma valid_sub28_5 : ∀ i : Fin 1, ValidAt (341 + i.val) := by decide +kernel
lemma valid_part28_5 : FiniteIntervals.Covers ValidAt 341 342 :=
  FiniteIntervals.of_fin 341 1 valid_sub28_5
lemma valid_sub28_6 : ∀ i : Fin 1, ValidAt (342 + i.val) := by decide +kernel
lemma valid_part28_6 : FiniteIntervals.Covers ValidAt 342 343 :=
  FiniteIntervals.of_fin 342 1 valid_sub28_6
lemma valid_sub28_7 : ∀ i : Fin 1, ValidAt (343 + i.val) := by decide +kernel
lemma valid_part28_7 : FiniteIntervals.Covers ValidAt 343 344 :=
  FiniteIntervals.of_fin 343 1 valid_sub28_7
lemma valid_sub28_8 : ∀ i : Fin 1, ValidAt (344 + i.val) := by decide +kernel
lemma valid_part28_8 : FiniteIntervals.Covers ValidAt 344 345 :=
  FiniteIntervals.of_fin 344 1 valid_sub28_8
lemma valid_sub28_9 : ∀ i : Fin 1, ValidAt (345 + i.val) := by decide +kernel
lemma valid_part28_9 : FiniteIntervals.Covers ValidAt 345 346 :=
  FiniteIntervals.of_fin 345 1 valid_sub28_9
lemma valid_sub28_10 : ∀ i : Fin 1, ValidAt (346 + i.val) := by decide +kernel
lemma valid_part28_10 : FiniteIntervals.Covers ValidAt 346 347 :=
  FiniteIntervals.of_fin 346 1 valid_sub28_10
lemma valid_sub28_11 : ∀ i : Fin 1, ValidAt (347 + i.val) := by decide +kernel
lemma valid_part28_11 : FiniteIntervals.Covers ValidAt 347 348 :=
  FiniteIntervals.of_fin 347 1 valid_sub28_11
lemma valid_interval28 : FiniteIntervals.Covers ValidAt 336 348 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part28_0 (FiniteIntervals.merge valid_part28_1 valid_part28_2)) (FiniteIntervals.merge valid_part28_3 (FiniteIntervals.merge valid_part28_4 valid_part28_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part28_6 (FiniteIntervals.merge valid_part28_7 valid_part28_8)) (FiniteIntervals.merge valid_part28_9 (FiniteIntervals.merge valid_part28_10 valid_part28_11))))
#print axioms valid_interval28
end Erdos184Work.PureSixActions0
