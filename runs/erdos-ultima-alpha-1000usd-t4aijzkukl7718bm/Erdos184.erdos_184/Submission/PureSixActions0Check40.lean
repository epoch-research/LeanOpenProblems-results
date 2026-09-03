import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub40_0 : ∀ i : Fin 1, ValidAt (480 + i.val) := by decide +kernel
lemma valid_part40_0 : FiniteIntervals.Covers ValidAt 480 481 :=
  FiniteIntervals.of_fin 480 1 valid_sub40_0
lemma valid_sub40_1 : ∀ i : Fin 1, ValidAt (481 + i.val) := by decide +kernel
lemma valid_part40_1 : FiniteIntervals.Covers ValidAt 481 482 :=
  FiniteIntervals.of_fin 481 1 valid_sub40_1
lemma valid_sub40_2 : ∀ i : Fin 1, ValidAt (482 + i.val) := by decide +kernel
lemma valid_part40_2 : FiniteIntervals.Covers ValidAt 482 483 :=
  FiniteIntervals.of_fin 482 1 valid_sub40_2
lemma valid_sub40_3 : ∀ i : Fin 1, ValidAt (483 + i.val) := by decide +kernel
lemma valid_part40_3 : FiniteIntervals.Covers ValidAt 483 484 :=
  FiniteIntervals.of_fin 483 1 valid_sub40_3
lemma valid_sub40_4 : ∀ i : Fin 1, ValidAt (484 + i.val) := by decide +kernel
lemma valid_part40_4 : FiniteIntervals.Covers ValidAt 484 485 :=
  FiniteIntervals.of_fin 484 1 valid_sub40_4
lemma valid_sub40_5 : ∀ i : Fin 1, ValidAt (485 + i.val) := by decide +kernel
lemma valid_part40_5 : FiniteIntervals.Covers ValidAt 485 486 :=
  FiniteIntervals.of_fin 485 1 valid_sub40_5
lemma valid_sub40_6 : ∀ i : Fin 1, ValidAt (486 + i.val) := by decide +kernel
lemma valid_part40_6 : FiniteIntervals.Covers ValidAt 486 487 :=
  FiniteIntervals.of_fin 486 1 valid_sub40_6
lemma valid_sub40_7 : ∀ i : Fin 1, ValidAt (487 + i.val) := by decide +kernel
lemma valid_part40_7 : FiniteIntervals.Covers ValidAt 487 488 :=
  FiniteIntervals.of_fin 487 1 valid_sub40_7
lemma valid_sub40_8 : ∀ i : Fin 1, ValidAt (488 + i.val) := by decide +kernel
lemma valid_part40_8 : FiniteIntervals.Covers ValidAt 488 489 :=
  FiniteIntervals.of_fin 488 1 valid_sub40_8
lemma valid_sub40_9 : ∀ i : Fin 1, ValidAt (489 + i.val) := by decide +kernel
lemma valid_part40_9 : FiniteIntervals.Covers ValidAt 489 490 :=
  FiniteIntervals.of_fin 489 1 valid_sub40_9
lemma valid_sub40_10 : ∀ i : Fin 1, ValidAt (490 + i.val) := by decide +kernel
lemma valid_part40_10 : FiniteIntervals.Covers ValidAt 490 491 :=
  FiniteIntervals.of_fin 490 1 valid_sub40_10
lemma valid_sub40_11 : ∀ i : Fin 1, ValidAt (491 + i.val) := by decide +kernel
lemma valid_part40_11 : FiniteIntervals.Covers ValidAt 491 492 :=
  FiniteIntervals.of_fin 491 1 valid_sub40_11
lemma valid_interval40 : FiniteIntervals.Covers ValidAt 480 492 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part40_0 (FiniteIntervals.merge valid_part40_1 valid_part40_2)) (FiniteIntervals.merge valid_part40_3 (FiniteIntervals.merge valid_part40_4 valid_part40_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part40_6 (FiniteIntervals.merge valid_part40_7 valid_part40_8)) (FiniteIntervals.merge valid_part40_9 (FiniteIntervals.merge valid_part40_10 valid_part40_11))))
#print axioms valid_interval40
end Erdos184Work.PureSixActions0
