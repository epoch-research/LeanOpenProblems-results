import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub53_0 : ∀ i : Fin 1, ValidAt (636 + i.val) := by decide +kernel
lemma valid_part53_0 : FiniteIntervals.Covers ValidAt 636 637 :=
  FiniteIntervals.of_fin 636 1 valid_sub53_0
lemma valid_sub53_1 : ∀ i : Fin 1, ValidAt (637 + i.val) := by decide +kernel
lemma valid_part53_1 : FiniteIntervals.Covers ValidAt 637 638 :=
  FiniteIntervals.of_fin 637 1 valid_sub53_1
lemma valid_sub53_2 : ∀ i : Fin 1, ValidAt (638 + i.val) := by decide +kernel
lemma valid_part53_2 : FiniteIntervals.Covers ValidAt 638 639 :=
  FiniteIntervals.of_fin 638 1 valid_sub53_2
lemma valid_sub53_3 : ∀ i : Fin 1, ValidAt (639 + i.val) := by decide +kernel
lemma valid_part53_3 : FiniteIntervals.Covers ValidAt 639 640 :=
  FiniteIntervals.of_fin 639 1 valid_sub53_3
lemma valid_sub53_4 : ∀ i : Fin 1, ValidAt (640 + i.val) := by decide +kernel
lemma valid_part53_4 : FiniteIntervals.Covers ValidAt 640 641 :=
  FiniteIntervals.of_fin 640 1 valid_sub53_4
lemma valid_sub53_5 : ∀ i : Fin 1, ValidAt (641 + i.val) := by decide +kernel
lemma valid_part53_5 : FiniteIntervals.Covers ValidAt 641 642 :=
  FiniteIntervals.of_fin 641 1 valid_sub53_5
lemma valid_sub53_6 : ∀ i : Fin 1, ValidAt (642 + i.val) := by decide +kernel
lemma valid_part53_6 : FiniteIntervals.Covers ValidAt 642 643 :=
  FiniteIntervals.of_fin 642 1 valid_sub53_6
lemma valid_sub53_7 : ∀ i : Fin 1, ValidAt (643 + i.val) := by decide +kernel
lemma valid_part53_7 : FiniteIntervals.Covers ValidAt 643 644 :=
  FiniteIntervals.of_fin 643 1 valid_sub53_7
lemma valid_sub53_8 : ∀ i : Fin 1, ValidAt (644 + i.val) := by decide +kernel
lemma valid_part53_8 : FiniteIntervals.Covers ValidAt 644 645 :=
  FiniteIntervals.of_fin 644 1 valid_sub53_8
lemma valid_sub53_9 : ∀ i : Fin 1, ValidAt (645 + i.val) := by decide +kernel
lemma valid_part53_9 : FiniteIntervals.Covers ValidAt 645 646 :=
  FiniteIntervals.of_fin 645 1 valid_sub53_9
lemma valid_sub53_10 : ∀ i : Fin 1, ValidAt (646 + i.val) := by decide +kernel
lemma valid_part53_10 : FiniteIntervals.Covers ValidAt 646 647 :=
  FiniteIntervals.of_fin 646 1 valid_sub53_10
lemma valid_sub53_11 : ∀ i : Fin 1, ValidAt (647 + i.val) := by decide +kernel
lemma valid_part53_11 : FiniteIntervals.Covers ValidAt 647 648 :=
  FiniteIntervals.of_fin 647 1 valid_sub53_11
lemma valid_interval53 : FiniteIntervals.Covers ValidAt 636 648 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part53_0 (FiniteIntervals.merge valid_part53_1 valid_part53_2)) (FiniteIntervals.merge valid_part53_3 (FiniteIntervals.merge valid_part53_4 valid_part53_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part53_6 (FiniteIntervals.merge valid_part53_7 valid_part53_8)) (FiniteIntervals.merge valid_part53_9 (FiniteIntervals.merge valid_part53_10 valid_part53_11))))
#print axioms valid_interval53
end Erdos184Work.PureSixActions0
