import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub56_0 : ∀ i : Fin 1, ValidAt (672 + i.val) := by decide +kernel
lemma valid_part56_0 : FiniteIntervals.Covers ValidAt 672 673 :=
  FiniteIntervals.of_fin 672 1 valid_sub56_0
lemma valid_sub56_1 : ∀ i : Fin 1, ValidAt (673 + i.val) := by decide +kernel
lemma valid_part56_1 : FiniteIntervals.Covers ValidAt 673 674 :=
  FiniteIntervals.of_fin 673 1 valid_sub56_1
lemma valid_sub56_2 : ∀ i : Fin 1, ValidAt (674 + i.val) := by decide +kernel
lemma valid_part56_2 : FiniteIntervals.Covers ValidAt 674 675 :=
  FiniteIntervals.of_fin 674 1 valid_sub56_2
lemma valid_sub56_3 : ∀ i : Fin 1, ValidAt (675 + i.val) := by decide +kernel
lemma valid_part56_3 : FiniteIntervals.Covers ValidAt 675 676 :=
  FiniteIntervals.of_fin 675 1 valid_sub56_3
lemma valid_sub56_4 : ∀ i : Fin 1, ValidAt (676 + i.val) := by decide +kernel
lemma valid_part56_4 : FiniteIntervals.Covers ValidAt 676 677 :=
  FiniteIntervals.of_fin 676 1 valid_sub56_4
lemma valid_sub56_5 : ∀ i : Fin 1, ValidAt (677 + i.val) := by decide +kernel
lemma valid_part56_5 : FiniteIntervals.Covers ValidAt 677 678 :=
  FiniteIntervals.of_fin 677 1 valid_sub56_5
lemma valid_sub56_6 : ∀ i : Fin 1, ValidAt (678 + i.val) := by decide +kernel
lemma valid_part56_6 : FiniteIntervals.Covers ValidAt 678 679 :=
  FiniteIntervals.of_fin 678 1 valid_sub56_6
lemma valid_sub56_7 : ∀ i : Fin 1, ValidAt (679 + i.val) := by decide +kernel
lemma valid_part56_7 : FiniteIntervals.Covers ValidAt 679 680 :=
  FiniteIntervals.of_fin 679 1 valid_sub56_7
lemma valid_sub56_8 : ∀ i : Fin 1, ValidAt (680 + i.val) := by decide +kernel
lemma valid_part56_8 : FiniteIntervals.Covers ValidAt 680 681 :=
  FiniteIntervals.of_fin 680 1 valid_sub56_8
lemma valid_sub56_9 : ∀ i : Fin 1, ValidAt (681 + i.val) := by decide +kernel
lemma valid_part56_9 : FiniteIntervals.Covers ValidAt 681 682 :=
  FiniteIntervals.of_fin 681 1 valid_sub56_9
lemma valid_sub56_10 : ∀ i : Fin 1, ValidAt (682 + i.val) := by decide +kernel
lemma valid_part56_10 : FiniteIntervals.Covers ValidAt 682 683 :=
  FiniteIntervals.of_fin 682 1 valid_sub56_10
lemma valid_sub56_11 : ∀ i : Fin 1, ValidAt (683 + i.val) := by decide +kernel
lemma valid_part56_11 : FiniteIntervals.Covers ValidAt 683 684 :=
  FiniteIntervals.of_fin 683 1 valid_sub56_11
lemma valid_interval56 : FiniteIntervals.Covers ValidAt 672 684 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part56_0 (FiniteIntervals.merge valid_part56_1 valid_part56_2)) (FiniteIntervals.merge valid_part56_3 (FiniteIntervals.merge valid_part56_4 valid_part56_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part56_6 (FiniteIntervals.merge valid_part56_7 valid_part56_8)) (FiniteIntervals.merge valid_part56_9 (FiniteIntervals.merge valid_part56_10 valid_part56_11))))
#print axioms valid_interval56
end Erdos184Work.PureSixActions0
