import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub52_0 : ∀ i : Fin 1, ValidAt (624 + i.val) := by decide +kernel
lemma valid_part52_0 : FiniteIntervals.Covers ValidAt 624 625 :=
  FiniteIntervals.of_fin 624 1 valid_sub52_0
lemma valid_sub52_1 : ∀ i : Fin 1, ValidAt (625 + i.val) := by decide +kernel
lemma valid_part52_1 : FiniteIntervals.Covers ValidAt 625 626 :=
  FiniteIntervals.of_fin 625 1 valid_sub52_1
lemma valid_sub52_2 : ∀ i : Fin 1, ValidAt (626 + i.val) := by decide +kernel
lemma valid_part52_2 : FiniteIntervals.Covers ValidAt 626 627 :=
  FiniteIntervals.of_fin 626 1 valid_sub52_2
lemma valid_sub52_3 : ∀ i : Fin 1, ValidAt (627 + i.val) := by decide +kernel
lemma valid_part52_3 : FiniteIntervals.Covers ValidAt 627 628 :=
  FiniteIntervals.of_fin 627 1 valid_sub52_3
lemma valid_sub52_4 : ∀ i : Fin 1, ValidAt (628 + i.val) := by decide +kernel
lemma valid_part52_4 : FiniteIntervals.Covers ValidAt 628 629 :=
  FiniteIntervals.of_fin 628 1 valid_sub52_4
lemma valid_sub52_5 : ∀ i : Fin 1, ValidAt (629 + i.val) := by decide +kernel
lemma valid_part52_5 : FiniteIntervals.Covers ValidAt 629 630 :=
  FiniteIntervals.of_fin 629 1 valid_sub52_5
lemma valid_sub52_6 : ∀ i : Fin 1, ValidAt (630 + i.val) := by decide +kernel
lemma valid_part52_6 : FiniteIntervals.Covers ValidAt 630 631 :=
  FiniteIntervals.of_fin 630 1 valid_sub52_6
lemma valid_sub52_7 : ∀ i : Fin 1, ValidAt (631 + i.val) := by decide +kernel
lemma valid_part52_7 : FiniteIntervals.Covers ValidAt 631 632 :=
  FiniteIntervals.of_fin 631 1 valid_sub52_7
lemma valid_sub52_8 : ∀ i : Fin 1, ValidAt (632 + i.val) := by decide +kernel
lemma valid_part52_8 : FiniteIntervals.Covers ValidAt 632 633 :=
  FiniteIntervals.of_fin 632 1 valid_sub52_8
lemma valid_sub52_9 : ∀ i : Fin 1, ValidAt (633 + i.val) := by decide +kernel
lemma valid_part52_9 : FiniteIntervals.Covers ValidAt 633 634 :=
  FiniteIntervals.of_fin 633 1 valid_sub52_9
lemma valid_sub52_10 : ∀ i : Fin 1, ValidAt (634 + i.val) := by decide +kernel
lemma valid_part52_10 : FiniteIntervals.Covers ValidAt 634 635 :=
  FiniteIntervals.of_fin 634 1 valid_sub52_10
lemma valid_sub52_11 : ∀ i : Fin 1, ValidAt (635 + i.val) := by decide +kernel
lemma valid_part52_11 : FiniteIntervals.Covers ValidAt 635 636 :=
  FiniteIntervals.of_fin 635 1 valid_sub52_11
lemma valid_interval52 : FiniteIntervals.Covers ValidAt 624 636 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part52_0 (FiniteIntervals.merge valid_part52_1 valid_part52_2)) (FiniteIntervals.merge valid_part52_3 (FiniteIntervals.merge valid_part52_4 valid_part52_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part52_6 (FiniteIntervals.merge valid_part52_7 valid_part52_8)) (FiniteIntervals.merge valid_part52_9 (FiniteIntervals.merge valid_part52_10 valid_part52_11))))
#print axioms valid_interval52
end Erdos184Work.PureSixActions0
