import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub54_0 : ∀ i : Fin 1, ValidAt (648 + i.val) := by decide +kernel
lemma valid_part54_0 : FiniteIntervals.Covers ValidAt 648 649 :=
  FiniteIntervals.of_fin 648 1 valid_sub54_0
lemma valid_sub54_1 : ∀ i : Fin 1, ValidAt (649 + i.val) := by decide +kernel
lemma valid_part54_1 : FiniteIntervals.Covers ValidAt 649 650 :=
  FiniteIntervals.of_fin 649 1 valid_sub54_1
lemma valid_sub54_2 : ∀ i : Fin 1, ValidAt (650 + i.val) := by decide +kernel
lemma valid_part54_2 : FiniteIntervals.Covers ValidAt 650 651 :=
  FiniteIntervals.of_fin 650 1 valid_sub54_2
lemma valid_sub54_3 : ∀ i : Fin 1, ValidAt (651 + i.val) := by decide +kernel
lemma valid_part54_3 : FiniteIntervals.Covers ValidAt 651 652 :=
  FiniteIntervals.of_fin 651 1 valid_sub54_3
lemma valid_sub54_4 : ∀ i : Fin 1, ValidAt (652 + i.val) := by decide +kernel
lemma valid_part54_4 : FiniteIntervals.Covers ValidAt 652 653 :=
  FiniteIntervals.of_fin 652 1 valid_sub54_4
lemma valid_sub54_5 : ∀ i : Fin 1, ValidAt (653 + i.val) := by decide +kernel
lemma valid_part54_5 : FiniteIntervals.Covers ValidAt 653 654 :=
  FiniteIntervals.of_fin 653 1 valid_sub54_5
lemma valid_sub54_6 : ∀ i : Fin 1, ValidAt (654 + i.val) := by decide +kernel
lemma valid_part54_6 : FiniteIntervals.Covers ValidAt 654 655 :=
  FiniteIntervals.of_fin 654 1 valid_sub54_6
lemma valid_sub54_7 : ∀ i : Fin 1, ValidAt (655 + i.val) := by decide +kernel
lemma valid_part54_7 : FiniteIntervals.Covers ValidAt 655 656 :=
  FiniteIntervals.of_fin 655 1 valid_sub54_7
lemma valid_sub54_8 : ∀ i : Fin 1, ValidAt (656 + i.val) := by decide +kernel
lemma valid_part54_8 : FiniteIntervals.Covers ValidAt 656 657 :=
  FiniteIntervals.of_fin 656 1 valid_sub54_8
lemma valid_sub54_9 : ∀ i : Fin 1, ValidAt (657 + i.val) := by decide +kernel
lemma valid_part54_9 : FiniteIntervals.Covers ValidAt 657 658 :=
  FiniteIntervals.of_fin 657 1 valid_sub54_9
lemma valid_sub54_10 : ∀ i : Fin 1, ValidAt (658 + i.val) := by decide +kernel
lemma valid_part54_10 : FiniteIntervals.Covers ValidAt 658 659 :=
  FiniteIntervals.of_fin 658 1 valid_sub54_10
lemma valid_sub54_11 : ∀ i : Fin 1, ValidAt (659 + i.val) := by decide +kernel
lemma valid_part54_11 : FiniteIntervals.Covers ValidAt 659 660 :=
  FiniteIntervals.of_fin 659 1 valid_sub54_11
lemma valid_interval54 : FiniteIntervals.Covers ValidAt 648 660 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part54_0 (FiniteIntervals.merge valid_part54_1 valid_part54_2)) (FiniteIntervals.merge valid_part54_3 (FiniteIntervals.merge valid_part54_4 valid_part54_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part54_6 (FiniteIntervals.merge valid_part54_7 valid_part54_8)) (FiniteIntervals.merge valid_part54_9 (FiniteIntervals.merge valid_part54_10 valid_part54_11))))
#print axioms valid_interval54
end Erdos184Work.PureSixActions0
