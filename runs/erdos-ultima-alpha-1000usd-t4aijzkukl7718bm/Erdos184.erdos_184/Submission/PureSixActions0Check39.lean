import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub39_0 : ∀ i : Fin 1, ValidAt (468 + i.val) := by decide +kernel
lemma valid_part39_0 : FiniteIntervals.Covers ValidAt 468 469 :=
  FiniteIntervals.of_fin 468 1 valid_sub39_0
lemma valid_sub39_1 : ∀ i : Fin 1, ValidAt (469 + i.val) := by decide +kernel
lemma valid_part39_1 : FiniteIntervals.Covers ValidAt 469 470 :=
  FiniteIntervals.of_fin 469 1 valid_sub39_1
lemma valid_sub39_2 : ∀ i : Fin 1, ValidAt (470 + i.val) := by decide +kernel
lemma valid_part39_2 : FiniteIntervals.Covers ValidAt 470 471 :=
  FiniteIntervals.of_fin 470 1 valid_sub39_2
lemma valid_sub39_3 : ∀ i : Fin 1, ValidAt (471 + i.val) := by decide +kernel
lemma valid_part39_3 : FiniteIntervals.Covers ValidAt 471 472 :=
  FiniteIntervals.of_fin 471 1 valid_sub39_3
lemma valid_sub39_4 : ∀ i : Fin 1, ValidAt (472 + i.val) := by decide +kernel
lemma valid_part39_4 : FiniteIntervals.Covers ValidAt 472 473 :=
  FiniteIntervals.of_fin 472 1 valid_sub39_4
lemma valid_sub39_5 : ∀ i : Fin 1, ValidAt (473 + i.val) := by decide +kernel
lemma valid_part39_5 : FiniteIntervals.Covers ValidAt 473 474 :=
  FiniteIntervals.of_fin 473 1 valid_sub39_5
lemma valid_sub39_6 : ∀ i : Fin 1, ValidAt (474 + i.val) := by decide +kernel
lemma valid_part39_6 : FiniteIntervals.Covers ValidAt 474 475 :=
  FiniteIntervals.of_fin 474 1 valid_sub39_6
lemma valid_sub39_7 : ∀ i : Fin 1, ValidAt (475 + i.val) := by decide +kernel
lemma valid_part39_7 : FiniteIntervals.Covers ValidAt 475 476 :=
  FiniteIntervals.of_fin 475 1 valid_sub39_7
lemma valid_sub39_8 : ∀ i : Fin 1, ValidAt (476 + i.val) := by decide +kernel
lemma valid_part39_8 : FiniteIntervals.Covers ValidAt 476 477 :=
  FiniteIntervals.of_fin 476 1 valid_sub39_8
lemma valid_sub39_9 : ∀ i : Fin 1, ValidAt (477 + i.val) := by decide +kernel
lemma valid_part39_9 : FiniteIntervals.Covers ValidAt 477 478 :=
  FiniteIntervals.of_fin 477 1 valid_sub39_9
lemma valid_sub39_10 : ∀ i : Fin 1, ValidAt (478 + i.val) := by decide +kernel
lemma valid_part39_10 : FiniteIntervals.Covers ValidAt 478 479 :=
  FiniteIntervals.of_fin 478 1 valid_sub39_10
lemma valid_sub39_11 : ∀ i : Fin 1, ValidAt (479 + i.val) := by decide +kernel
lemma valid_part39_11 : FiniteIntervals.Covers ValidAt 479 480 :=
  FiniteIntervals.of_fin 479 1 valid_sub39_11
lemma valid_interval39 : FiniteIntervals.Covers ValidAt 468 480 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part39_0 (FiniteIntervals.merge valid_part39_1 valid_part39_2)) (FiniteIntervals.merge valid_part39_3 (FiniteIntervals.merge valid_part39_4 valid_part39_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part39_6 (FiniteIntervals.merge valid_part39_7 valid_part39_8)) (FiniteIntervals.merge valid_part39_9 (FiniteIntervals.merge valid_part39_10 valid_part39_11))))
#print axioms valid_interval39
end Erdos184Work.PureSixActions0
