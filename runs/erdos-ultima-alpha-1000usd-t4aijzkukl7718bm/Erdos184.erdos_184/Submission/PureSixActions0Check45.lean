import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub45_0 : ∀ i : Fin 1, ValidAt (540 + i.val) := by decide +kernel
lemma valid_part45_0 : FiniteIntervals.Covers ValidAt 540 541 :=
  FiniteIntervals.of_fin 540 1 valid_sub45_0
lemma valid_sub45_1 : ∀ i : Fin 1, ValidAt (541 + i.val) := by decide +kernel
lemma valid_part45_1 : FiniteIntervals.Covers ValidAt 541 542 :=
  FiniteIntervals.of_fin 541 1 valid_sub45_1
lemma valid_sub45_2 : ∀ i : Fin 1, ValidAt (542 + i.val) := by decide +kernel
lemma valid_part45_2 : FiniteIntervals.Covers ValidAt 542 543 :=
  FiniteIntervals.of_fin 542 1 valid_sub45_2
lemma valid_sub45_3 : ∀ i : Fin 1, ValidAt (543 + i.val) := by decide +kernel
lemma valid_part45_3 : FiniteIntervals.Covers ValidAt 543 544 :=
  FiniteIntervals.of_fin 543 1 valid_sub45_3
lemma valid_sub45_4 : ∀ i : Fin 1, ValidAt (544 + i.val) := by decide +kernel
lemma valid_part45_4 : FiniteIntervals.Covers ValidAt 544 545 :=
  FiniteIntervals.of_fin 544 1 valid_sub45_4
lemma valid_sub45_5 : ∀ i : Fin 1, ValidAt (545 + i.val) := by decide +kernel
lemma valid_part45_5 : FiniteIntervals.Covers ValidAt 545 546 :=
  FiniteIntervals.of_fin 545 1 valid_sub45_5
lemma valid_sub45_6 : ∀ i : Fin 1, ValidAt (546 + i.val) := by decide +kernel
lemma valid_part45_6 : FiniteIntervals.Covers ValidAt 546 547 :=
  FiniteIntervals.of_fin 546 1 valid_sub45_6
lemma valid_sub45_7 : ∀ i : Fin 1, ValidAt (547 + i.val) := by decide +kernel
lemma valid_part45_7 : FiniteIntervals.Covers ValidAt 547 548 :=
  FiniteIntervals.of_fin 547 1 valid_sub45_7
lemma valid_sub45_8 : ∀ i : Fin 1, ValidAt (548 + i.val) := by decide +kernel
lemma valid_part45_8 : FiniteIntervals.Covers ValidAt 548 549 :=
  FiniteIntervals.of_fin 548 1 valid_sub45_8
lemma valid_sub45_9 : ∀ i : Fin 1, ValidAt (549 + i.val) := by decide +kernel
lemma valid_part45_9 : FiniteIntervals.Covers ValidAt 549 550 :=
  FiniteIntervals.of_fin 549 1 valid_sub45_9
lemma valid_sub45_10 : ∀ i : Fin 1, ValidAt (550 + i.val) := by decide +kernel
lemma valid_part45_10 : FiniteIntervals.Covers ValidAt 550 551 :=
  FiniteIntervals.of_fin 550 1 valid_sub45_10
lemma valid_sub45_11 : ∀ i : Fin 1, ValidAt (551 + i.val) := by decide +kernel
lemma valid_part45_11 : FiniteIntervals.Covers ValidAt 551 552 :=
  FiniteIntervals.of_fin 551 1 valid_sub45_11
lemma valid_interval45 : FiniteIntervals.Covers ValidAt 540 552 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part45_0 (FiniteIntervals.merge valid_part45_1 valid_part45_2)) (FiniteIntervals.merge valid_part45_3 (FiniteIntervals.merge valid_part45_4 valid_part45_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part45_6 (FiniteIntervals.merge valid_part45_7 valid_part45_8)) (FiniteIntervals.merge valid_part45_9 (FiniteIntervals.merge valid_part45_10 valid_part45_11))))
#print axioms valid_interval45
end Erdos184Work.PureSixActions0
