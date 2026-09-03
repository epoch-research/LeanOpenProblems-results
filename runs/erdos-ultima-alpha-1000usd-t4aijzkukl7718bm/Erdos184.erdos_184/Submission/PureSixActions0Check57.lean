import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub57_0 : ∀ i : Fin 1, ValidAt (684 + i.val) := by decide +kernel
lemma valid_part57_0 : FiniteIntervals.Covers ValidAt 684 685 :=
  FiniteIntervals.of_fin 684 1 valid_sub57_0
lemma valid_sub57_1 : ∀ i : Fin 1, ValidAt (685 + i.val) := by decide +kernel
lemma valid_part57_1 : FiniteIntervals.Covers ValidAt 685 686 :=
  FiniteIntervals.of_fin 685 1 valid_sub57_1
lemma valid_sub57_2 : ∀ i : Fin 1, ValidAt (686 + i.val) := by decide +kernel
lemma valid_part57_2 : FiniteIntervals.Covers ValidAt 686 687 :=
  FiniteIntervals.of_fin 686 1 valid_sub57_2
lemma valid_sub57_3 : ∀ i : Fin 1, ValidAt (687 + i.val) := by decide +kernel
lemma valid_part57_3 : FiniteIntervals.Covers ValidAt 687 688 :=
  FiniteIntervals.of_fin 687 1 valid_sub57_3
lemma valid_sub57_4 : ∀ i : Fin 1, ValidAt (688 + i.val) := by decide +kernel
lemma valid_part57_4 : FiniteIntervals.Covers ValidAt 688 689 :=
  FiniteIntervals.of_fin 688 1 valid_sub57_4
lemma valid_sub57_5 : ∀ i : Fin 1, ValidAt (689 + i.val) := by decide +kernel
lemma valid_part57_5 : FiniteIntervals.Covers ValidAt 689 690 :=
  FiniteIntervals.of_fin 689 1 valid_sub57_5
lemma valid_sub57_6 : ∀ i : Fin 1, ValidAt (690 + i.val) := by decide +kernel
lemma valid_part57_6 : FiniteIntervals.Covers ValidAt 690 691 :=
  FiniteIntervals.of_fin 690 1 valid_sub57_6
lemma valid_sub57_7 : ∀ i : Fin 1, ValidAt (691 + i.val) := by decide +kernel
lemma valid_part57_7 : FiniteIntervals.Covers ValidAt 691 692 :=
  FiniteIntervals.of_fin 691 1 valid_sub57_7
lemma valid_sub57_8 : ∀ i : Fin 1, ValidAt (692 + i.val) := by decide +kernel
lemma valid_part57_8 : FiniteIntervals.Covers ValidAt 692 693 :=
  FiniteIntervals.of_fin 692 1 valid_sub57_8
lemma valid_sub57_9 : ∀ i : Fin 1, ValidAt (693 + i.val) := by decide +kernel
lemma valid_part57_9 : FiniteIntervals.Covers ValidAt 693 694 :=
  FiniteIntervals.of_fin 693 1 valid_sub57_9
lemma valid_sub57_10 : ∀ i : Fin 1, ValidAt (694 + i.val) := by decide +kernel
lemma valid_part57_10 : FiniteIntervals.Covers ValidAt 694 695 :=
  FiniteIntervals.of_fin 694 1 valid_sub57_10
lemma valid_sub57_11 : ∀ i : Fin 1, ValidAt (695 + i.val) := by decide +kernel
lemma valid_part57_11 : FiniteIntervals.Covers ValidAt 695 696 :=
  FiniteIntervals.of_fin 695 1 valid_sub57_11
lemma valid_interval57 : FiniteIntervals.Covers ValidAt 684 696 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part57_0 (FiniteIntervals.merge valid_part57_1 valid_part57_2)) (FiniteIntervals.merge valid_part57_3 (FiniteIntervals.merge valid_part57_4 valid_part57_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part57_6 (FiniteIntervals.merge valid_part57_7 valid_part57_8)) (FiniteIntervals.merge valid_part57_9 (FiniteIntervals.merge valid_part57_10 valid_part57_11))))
#print axioms valid_interval57
end Erdos184Work.PureSixActions0
