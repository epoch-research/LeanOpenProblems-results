import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub50_0 : ∀ i : Fin 1, ValidAt (600 + i.val) := by decide +kernel
lemma valid_part50_0 : FiniteIntervals.Covers ValidAt 600 601 :=
  FiniteIntervals.of_fin 600 1 valid_sub50_0
lemma valid_sub50_1 : ∀ i : Fin 1, ValidAt (601 + i.val) := by decide +kernel
lemma valid_part50_1 : FiniteIntervals.Covers ValidAt 601 602 :=
  FiniteIntervals.of_fin 601 1 valid_sub50_1
lemma valid_sub50_2 : ∀ i : Fin 1, ValidAt (602 + i.val) := by decide +kernel
lemma valid_part50_2 : FiniteIntervals.Covers ValidAt 602 603 :=
  FiniteIntervals.of_fin 602 1 valid_sub50_2
lemma valid_sub50_3 : ∀ i : Fin 1, ValidAt (603 + i.val) := by decide +kernel
lemma valid_part50_3 : FiniteIntervals.Covers ValidAt 603 604 :=
  FiniteIntervals.of_fin 603 1 valid_sub50_3
lemma valid_sub50_4 : ∀ i : Fin 1, ValidAt (604 + i.val) := by decide +kernel
lemma valid_part50_4 : FiniteIntervals.Covers ValidAt 604 605 :=
  FiniteIntervals.of_fin 604 1 valid_sub50_4
lemma valid_sub50_5 : ∀ i : Fin 1, ValidAt (605 + i.val) := by decide +kernel
lemma valid_part50_5 : FiniteIntervals.Covers ValidAt 605 606 :=
  FiniteIntervals.of_fin 605 1 valid_sub50_5
lemma valid_sub50_6 : ∀ i : Fin 1, ValidAt (606 + i.val) := by decide +kernel
lemma valid_part50_6 : FiniteIntervals.Covers ValidAt 606 607 :=
  FiniteIntervals.of_fin 606 1 valid_sub50_6
lemma valid_sub50_7 : ∀ i : Fin 1, ValidAt (607 + i.val) := by decide +kernel
lemma valid_part50_7 : FiniteIntervals.Covers ValidAt 607 608 :=
  FiniteIntervals.of_fin 607 1 valid_sub50_7
lemma valid_sub50_8 : ∀ i : Fin 1, ValidAt (608 + i.val) := by decide +kernel
lemma valid_part50_8 : FiniteIntervals.Covers ValidAt 608 609 :=
  FiniteIntervals.of_fin 608 1 valid_sub50_8
lemma valid_sub50_9 : ∀ i : Fin 1, ValidAt (609 + i.val) := by decide +kernel
lemma valid_part50_9 : FiniteIntervals.Covers ValidAt 609 610 :=
  FiniteIntervals.of_fin 609 1 valid_sub50_9
lemma valid_sub50_10 : ∀ i : Fin 1, ValidAt (610 + i.val) := by decide +kernel
lemma valid_part50_10 : FiniteIntervals.Covers ValidAt 610 611 :=
  FiniteIntervals.of_fin 610 1 valid_sub50_10
lemma valid_sub50_11 : ∀ i : Fin 1, ValidAt (611 + i.val) := by decide +kernel
lemma valid_part50_11 : FiniteIntervals.Covers ValidAt 611 612 :=
  FiniteIntervals.of_fin 611 1 valid_sub50_11
lemma valid_interval50 : FiniteIntervals.Covers ValidAt 600 612 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part50_0 (FiniteIntervals.merge valid_part50_1 valid_part50_2)) (FiniteIntervals.merge valid_part50_3 (FiniteIntervals.merge valid_part50_4 valid_part50_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part50_6 (FiniteIntervals.merge valid_part50_7 valid_part50_8)) (FiniteIntervals.merge valid_part50_9 (FiniteIntervals.merge valid_part50_10 valid_part50_11))))
#print axioms valid_interval50
end Erdos184Work.PureSixActions0
