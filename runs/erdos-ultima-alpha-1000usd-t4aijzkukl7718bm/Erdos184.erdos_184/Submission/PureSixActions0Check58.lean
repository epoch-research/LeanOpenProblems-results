import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub58_0 : ∀ i : Fin 1, ValidAt (696 + i.val) := by decide +kernel
lemma valid_part58_0 : FiniteIntervals.Covers ValidAt 696 697 :=
  FiniteIntervals.of_fin 696 1 valid_sub58_0
lemma valid_sub58_1 : ∀ i : Fin 1, ValidAt (697 + i.val) := by decide +kernel
lemma valid_part58_1 : FiniteIntervals.Covers ValidAt 697 698 :=
  FiniteIntervals.of_fin 697 1 valid_sub58_1
lemma valid_sub58_2 : ∀ i : Fin 1, ValidAt (698 + i.val) := by decide +kernel
lemma valid_part58_2 : FiniteIntervals.Covers ValidAt 698 699 :=
  FiniteIntervals.of_fin 698 1 valid_sub58_2
lemma valid_sub58_3 : ∀ i : Fin 1, ValidAt (699 + i.val) := by decide +kernel
lemma valid_part58_3 : FiniteIntervals.Covers ValidAt 699 700 :=
  FiniteIntervals.of_fin 699 1 valid_sub58_3
lemma valid_sub58_4 : ∀ i : Fin 1, ValidAt (700 + i.val) := by decide +kernel
lemma valid_part58_4 : FiniteIntervals.Covers ValidAt 700 701 :=
  FiniteIntervals.of_fin 700 1 valid_sub58_4
lemma valid_sub58_5 : ∀ i : Fin 1, ValidAt (701 + i.val) := by decide +kernel
lemma valid_part58_5 : FiniteIntervals.Covers ValidAt 701 702 :=
  FiniteIntervals.of_fin 701 1 valid_sub58_5
lemma valid_sub58_6 : ∀ i : Fin 1, ValidAt (702 + i.val) := by decide +kernel
lemma valid_part58_6 : FiniteIntervals.Covers ValidAt 702 703 :=
  FiniteIntervals.of_fin 702 1 valid_sub58_6
lemma valid_sub58_7 : ∀ i : Fin 1, ValidAt (703 + i.val) := by decide +kernel
lemma valid_part58_7 : FiniteIntervals.Covers ValidAt 703 704 :=
  FiniteIntervals.of_fin 703 1 valid_sub58_7
lemma valid_sub58_8 : ∀ i : Fin 1, ValidAt (704 + i.val) := by decide +kernel
lemma valid_part58_8 : FiniteIntervals.Covers ValidAt 704 705 :=
  FiniteIntervals.of_fin 704 1 valid_sub58_8
lemma valid_sub58_9 : ∀ i : Fin 1, ValidAt (705 + i.val) := by decide +kernel
lemma valid_part58_9 : FiniteIntervals.Covers ValidAt 705 706 :=
  FiniteIntervals.of_fin 705 1 valid_sub58_9
lemma valid_sub58_10 : ∀ i : Fin 1, ValidAt (706 + i.val) := by decide +kernel
lemma valid_part58_10 : FiniteIntervals.Covers ValidAt 706 707 :=
  FiniteIntervals.of_fin 706 1 valid_sub58_10
lemma valid_sub58_11 : ∀ i : Fin 1, ValidAt (707 + i.val) := by decide +kernel
lemma valid_part58_11 : FiniteIntervals.Covers ValidAt 707 708 :=
  FiniteIntervals.of_fin 707 1 valid_sub58_11
lemma valid_interval58 : FiniteIntervals.Covers ValidAt 696 708 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part58_0 (FiniteIntervals.merge valid_part58_1 valid_part58_2)) (FiniteIntervals.merge valid_part58_3 (FiniteIntervals.merge valid_part58_4 valid_part58_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part58_6 (FiniteIntervals.merge valid_part58_7 valid_part58_8)) (FiniteIntervals.merge valid_part58_9 (FiniteIntervals.merge valid_part58_10 valid_part58_11))))
#print axioms valid_interval58
end Erdos184Work.PureSixActions0
