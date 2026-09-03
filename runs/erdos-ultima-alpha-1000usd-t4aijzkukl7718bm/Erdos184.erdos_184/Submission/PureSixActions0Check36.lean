import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub36_0 : ∀ i : Fin 1, ValidAt (432 + i.val) := by decide +kernel
lemma valid_part36_0 : FiniteIntervals.Covers ValidAt 432 433 :=
  FiniteIntervals.of_fin 432 1 valid_sub36_0
lemma valid_sub36_1 : ∀ i : Fin 1, ValidAt (433 + i.val) := by decide +kernel
lemma valid_part36_1 : FiniteIntervals.Covers ValidAt 433 434 :=
  FiniteIntervals.of_fin 433 1 valid_sub36_1
lemma valid_sub36_2 : ∀ i : Fin 1, ValidAt (434 + i.val) := by decide +kernel
lemma valid_part36_2 : FiniteIntervals.Covers ValidAt 434 435 :=
  FiniteIntervals.of_fin 434 1 valid_sub36_2
lemma valid_sub36_3 : ∀ i : Fin 1, ValidAt (435 + i.val) := by decide +kernel
lemma valid_part36_3 : FiniteIntervals.Covers ValidAt 435 436 :=
  FiniteIntervals.of_fin 435 1 valid_sub36_3
lemma valid_sub36_4 : ∀ i : Fin 1, ValidAt (436 + i.val) := by decide +kernel
lemma valid_part36_4 : FiniteIntervals.Covers ValidAt 436 437 :=
  FiniteIntervals.of_fin 436 1 valid_sub36_4
lemma valid_sub36_5 : ∀ i : Fin 1, ValidAt (437 + i.val) := by decide +kernel
lemma valid_part36_5 : FiniteIntervals.Covers ValidAt 437 438 :=
  FiniteIntervals.of_fin 437 1 valid_sub36_5
lemma valid_sub36_6 : ∀ i : Fin 1, ValidAt (438 + i.val) := by decide +kernel
lemma valid_part36_6 : FiniteIntervals.Covers ValidAt 438 439 :=
  FiniteIntervals.of_fin 438 1 valid_sub36_6
lemma valid_sub36_7 : ∀ i : Fin 1, ValidAt (439 + i.val) := by decide +kernel
lemma valid_part36_7 : FiniteIntervals.Covers ValidAt 439 440 :=
  FiniteIntervals.of_fin 439 1 valid_sub36_7
lemma valid_sub36_8 : ∀ i : Fin 1, ValidAt (440 + i.val) := by decide +kernel
lemma valid_part36_8 : FiniteIntervals.Covers ValidAt 440 441 :=
  FiniteIntervals.of_fin 440 1 valid_sub36_8
lemma valid_sub36_9 : ∀ i : Fin 1, ValidAt (441 + i.val) := by decide +kernel
lemma valid_part36_9 : FiniteIntervals.Covers ValidAt 441 442 :=
  FiniteIntervals.of_fin 441 1 valid_sub36_9
lemma valid_sub36_10 : ∀ i : Fin 1, ValidAt (442 + i.val) := by decide +kernel
lemma valid_part36_10 : FiniteIntervals.Covers ValidAt 442 443 :=
  FiniteIntervals.of_fin 442 1 valid_sub36_10
lemma valid_sub36_11 : ∀ i : Fin 1, ValidAt (443 + i.val) := by decide +kernel
lemma valid_part36_11 : FiniteIntervals.Covers ValidAt 443 444 :=
  FiniteIntervals.of_fin 443 1 valid_sub36_11
lemma valid_interval36 : FiniteIntervals.Covers ValidAt 432 444 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part36_0 (FiniteIntervals.merge valid_part36_1 valid_part36_2)) (FiniteIntervals.merge valid_part36_3 (FiniteIntervals.merge valid_part36_4 valid_part36_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part36_6 (FiniteIntervals.merge valid_part36_7 valid_part36_8)) (FiniteIntervals.merge valid_part36_9 (FiniteIntervals.merge valid_part36_10 valid_part36_11))))
#print axioms valid_interval36
end Erdos184Work.PureSixActions0
