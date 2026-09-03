import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub47_0 : ∀ i : Fin 1, ValidAt (564 + i.val) := by decide +kernel
lemma valid_part47_0 : FiniteIntervals.Covers ValidAt 564 565 :=
  FiniteIntervals.of_fin 564 1 valid_sub47_0
lemma valid_sub47_1 : ∀ i : Fin 1, ValidAt (565 + i.val) := by decide +kernel
lemma valid_part47_1 : FiniteIntervals.Covers ValidAt 565 566 :=
  FiniteIntervals.of_fin 565 1 valid_sub47_1
lemma valid_sub47_2 : ∀ i : Fin 1, ValidAt (566 + i.val) := by decide +kernel
lemma valid_part47_2 : FiniteIntervals.Covers ValidAt 566 567 :=
  FiniteIntervals.of_fin 566 1 valid_sub47_2
lemma valid_sub47_3 : ∀ i : Fin 1, ValidAt (567 + i.val) := by decide +kernel
lemma valid_part47_3 : FiniteIntervals.Covers ValidAt 567 568 :=
  FiniteIntervals.of_fin 567 1 valid_sub47_3
lemma valid_sub47_4 : ∀ i : Fin 1, ValidAt (568 + i.val) := by decide +kernel
lemma valid_part47_4 : FiniteIntervals.Covers ValidAt 568 569 :=
  FiniteIntervals.of_fin 568 1 valid_sub47_4
lemma valid_sub47_5 : ∀ i : Fin 1, ValidAt (569 + i.val) := by decide +kernel
lemma valid_part47_5 : FiniteIntervals.Covers ValidAt 569 570 :=
  FiniteIntervals.of_fin 569 1 valid_sub47_5
lemma valid_sub47_6 : ∀ i : Fin 1, ValidAt (570 + i.val) := by decide +kernel
lemma valid_part47_6 : FiniteIntervals.Covers ValidAt 570 571 :=
  FiniteIntervals.of_fin 570 1 valid_sub47_6
lemma valid_sub47_7 : ∀ i : Fin 1, ValidAt (571 + i.val) := by decide +kernel
lemma valid_part47_7 : FiniteIntervals.Covers ValidAt 571 572 :=
  FiniteIntervals.of_fin 571 1 valid_sub47_7
lemma valid_sub47_8 : ∀ i : Fin 1, ValidAt (572 + i.val) := by decide +kernel
lemma valid_part47_8 : FiniteIntervals.Covers ValidAt 572 573 :=
  FiniteIntervals.of_fin 572 1 valid_sub47_8
lemma valid_sub47_9 : ∀ i : Fin 1, ValidAt (573 + i.val) := by decide +kernel
lemma valid_part47_9 : FiniteIntervals.Covers ValidAt 573 574 :=
  FiniteIntervals.of_fin 573 1 valid_sub47_9
lemma valid_sub47_10 : ∀ i : Fin 1, ValidAt (574 + i.val) := by decide +kernel
lemma valid_part47_10 : FiniteIntervals.Covers ValidAt 574 575 :=
  FiniteIntervals.of_fin 574 1 valid_sub47_10
lemma valid_sub47_11 : ∀ i : Fin 1, ValidAt (575 + i.val) := by decide +kernel
lemma valid_part47_11 : FiniteIntervals.Covers ValidAt 575 576 :=
  FiniteIntervals.of_fin 575 1 valid_sub47_11
lemma valid_interval47 : FiniteIntervals.Covers ValidAt 564 576 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part47_0 (FiniteIntervals.merge valid_part47_1 valid_part47_2)) (FiniteIntervals.merge valid_part47_3 (FiniteIntervals.merge valid_part47_4 valid_part47_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part47_6 (FiniteIntervals.merge valid_part47_7 valid_part47_8)) (FiniteIntervals.merge valid_part47_9 (FiniteIntervals.merge valid_part47_10 valid_part47_11))))
#print axioms valid_interval47
end Erdos184Work.PureSixActions0
