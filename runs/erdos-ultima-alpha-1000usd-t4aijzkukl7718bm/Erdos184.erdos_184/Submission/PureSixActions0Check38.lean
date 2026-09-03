import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub38_0 : ∀ i : Fin 1, ValidAt (456 + i.val) := by decide +kernel
lemma valid_part38_0 : FiniteIntervals.Covers ValidAt 456 457 :=
  FiniteIntervals.of_fin 456 1 valid_sub38_0
lemma valid_sub38_1 : ∀ i : Fin 1, ValidAt (457 + i.val) := by decide +kernel
lemma valid_part38_1 : FiniteIntervals.Covers ValidAt 457 458 :=
  FiniteIntervals.of_fin 457 1 valid_sub38_1
lemma valid_sub38_2 : ∀ i : Fin 1, ValidAt (458 + i.val) := by decide +kernel
lemma valid_part38_2 : FiniteIntervals.Covers ValidAt 458 459 :=
  FiniteIntervals.of_fin 458 1 valid_sub38_2
lemma valid_sub38_3 : ∀ i : Fin 1, ValidAt (459 + i.val) := by decide +kernel
lemma valid_part38_3 : FiniteIntervals.Covers ValidAt 459 460 :=
  FiniteIntervals.of_fin 459 1 valid_sub38_3
lemma valid_sub38_4 : ∀ i : Fin 1, ValidAt (460 + i.val) := by decide +kernel
lemma valid_part38_4 : FiniteIntervals.Covers ValidAt 460 461 :=
  FiniteIntervals.of_fin 460 1 valid_sub38_4
lemma valid_sub38_5 : ∀ i : Fin 1, ValidAt (461 + i.val) := by decide +kernel
lemma valid_part38_5 : FiniteIntervals.Covers ValidAt 461 462 :=
  FiniteIntervals.of_fin 461 1 valid_sub38_5
lemma valid_sub38_6 : ∀ i : Fin 1, ValidAt (462 + i.val) := by decide +kernel
lemma valid_part38_6 : FiniteIntervals.Covers ValidAt 462 463 :=
  FiniteIntervals.of_fin 462 1 valid_sub38_6
lemma valid_sub38_7 : ∀ i : Fin 1, ValidAt (463 + i.val) := by decide +kernel
lemma valid_part38_7 : FiniteIntervals.Covers ValidAt 463 464 :=
  FiniteIntervals.of_fin 463 1 valid_sub38_7
lemma valid_sub38_8 : ∀ i : Fin 1, ValidAt (464 + i.val) := by decide +kernel
lemma valid_part38_8 : FiniteIntervals.Covers ValidAt 464 465 :=
  FiniteIntervals.of_fin 464 1 valid_sub38_8
lemma valid_sub38_9 : ∀ i : Fin 1, ValidAt (465 + i.val) := by decide +kernel
lemma valid_part38_9 : FiniteIntervals.Covers ValidAt 465 466 :=
  FiniteIntervals.of_fin 465 1 valid_sub38_9
lemma valid_sub38_10 : ∀ i : Fin 1, ValidAt (466 + i.val) := by decide +kernel
lemma valid_part38_10 : FiniteIntervals.Covers ValidAt 466 467 :=
  FiniteIntervals.of_fin 466 1 valid_sub38_10
lemma valid_sub38_11 : ∀ i : Fin 1, ValidAt (467 + i.val) := by decide +kernel
lemma valid_part38_11 : FiniteIntervals.Covers ValidAt 467 468 :=
  FiniteIntervals.of_fin 467 1 valid_sub38_11
lemma valid_interval38 : FiniteIntervals.Covers ValidAt 456 468 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part38_0 (FiniteIntervals.merge valid_part38_1 valid_part38_2)) (FiniteIntervals.merge valid_part38_3 (FiniteIntervals.merge valid_part38_4 valid_part38_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part38_6 (FiniteIntervals.merge valid_part38_7 valid_part38_8)) (FiniteIntervals.merge valid_part38_9 (FiniteIntervals.merge valid_part38_10 valid_part38_11))))
#print axioms valid_interval38
end Erdos184Work.PureSixActions0
