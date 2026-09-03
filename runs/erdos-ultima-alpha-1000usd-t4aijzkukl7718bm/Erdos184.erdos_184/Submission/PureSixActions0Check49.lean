import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub49_0 : ∀ i : Fin 1, ValidAt (588 + i.val) := by decide +kernel
lemma valid_part49_0 : FiniteIntervals.Covers ValidAt 588 589 :=
  FiniteIntervals.of_fin 588 1 valid_sub49_0
lemma valid_sub49_1 : ∀ i : Fin 1, ValidAt (589 + i.val) := by decide +kernel
lemma valid_part49_1 : FiniteIntervals.Covers ValidAt 589 590 :=
  FiniteIntervals.of_fin 589 1 valid_sub49_1
lemma valid_sub49_2 : ∀ i : Fin 1, ValidAt (590 + i.val) := by decide +kernel
lemma valid_part49_2 : FiniteIntervals.Covers ValidAt 590 591 :=
  FiniteIntervals.of_fin 590 1 valid_sub49_2
lemma valid_sub49_3 : ∀ i : Fin 1, ValidAt (591 + i.val) := by decide +kernel
lemma valid_part49_3 : FiniteIntervals.Covers ValidAt 591 592 :=
  FiniteIntervals.of_fin 591 1 valid_sub49_3
lemma valid_sub49_4 : ∀ i : Fin 1, ValidAt (592 + i.val) := by decide +kernel
lemma valid_part49_4 : FiniteIntervals.Covers ValidAt 592 593 :=
  FiniteIntervals.of_fin 592 1 valid_sub49_4
lemma valid_sub49_5 : ∀ i : Fin 1, ValidAt (593 + i.val) := by decide +kernel
lemma valid_part49_5 : FiniteIntervals.Covers ValidAt 593 594 :=
  FiniteIntervals.of_fin 593 1 valid_sub49_5
lemma valid_sub49_6 : ∀ i : Fin 1, ValidAt (594 + i.val) := by decide +kernel
lemma valid_part49_6 : FiniteIntervals.Covers ValidAt 594 595 :=
  FiniteIntervals.of_fin 594 1 valid_sub49_6
lemma valid_sub49_7 : ∀ i : Fin 1, ValidAt (595 + i.val) := by decide +kernel
lemma valid_part49_7 : FiniteIntervals.Covers ValidAt 595 596 :=
  FiniteIntervals.of_fin 595 1 valid_sub49_7
lemma valid_sub49_8 : ∀ i : Fin 1, ValidAt (596 + i.val) := by decide +kernel
lemma valid_part49_8 : FiniteIntervals.Covers ValidAt 596 597 :=
  FiniteIntervals.of_fin 596 1 valid_sub49_8
lemma valid_sub49_9 : ∀ i : Fin 1, ValidAt (597 + i.val) := by decide +kernel
lemma valid_part49_9 : FiniteIntervals.Covers ValidAt 597 598 :=
  FiniteIntervals.of_fin 597 1 valid_sub49_9
lemma valid_sub49_10 : ∀ i : Fin 1, ValidAt (598 + i.val) := by decide +kernel
lemma valid_part49_10 : FiniteIntervals.Covers ValidAt 598 599 :=
  FiniteIntervals.of_fin 598 1 valid_sub49_10
lemma valid_sub49_11 : ∀ i : Fin 1, ValidAt (599 + i.val) := by decide +kernel
lemma valid_part49_11 : FiniteIntervals.Covers ValidAt 599 600 :=
  FiniteIntervals.of_fin 599 1 valid_sub49_11
lemma valid_interval49 : FiniteIntervals.Covers ValidAt 588 600 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part49_0 (FiniteIntervals.merge valid_part49_1 valid_part49_2)) (FiniteIntervals.merge valid_part49_3 (FiniteIntervals.merge valid_part49_4 valid_part49_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part49_6 (FiniteIntervals.merge valid_part49_7 valid_part49_8)) (FiniteIntervals.merge valid_part49_9 (FiniteIntervals.merge valid_part49_10 valid_part49_11))))
#print axioms valid_interval49
end Erdos184Work.PureSixActions0
