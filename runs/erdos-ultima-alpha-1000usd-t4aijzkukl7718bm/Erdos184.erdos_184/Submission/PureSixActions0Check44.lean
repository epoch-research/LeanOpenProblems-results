import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub44_0 : ∀ i : Fin 1, ValidAt (528 + i.val) := by decide +kernel
lemma valid_part44_0 : FiniteIntervals.Covers ValidAt 528 529 :=
  FiniteIntervals.of_fin 528 1 valid_sub44_0
lemma valid_sub44_1 : ∀ i : Fin 1, ValidAt (529 + i.val) := by decide +kernel
lemma valid_part44_1 : FiniteIntervals.Covers ValidAt 529 530 :=
  FiniteIntervals.of_fin 529 1 valid_sub44_1
lemma valid_sub44_2 : ∀ i : Fin 1, ValidAt (530 + i.val) := by decide +kernel
lemma valid_part44_2 : FiniteIntervals.Covers ValidAt 530 531 :=
  FiniteIntervals.of_fin 530 1 valid_sub44_2
lemma valid_sub44_3 : ∀ i : Fin 1, ValidAt (531 + i.val) := by decide +kernel
lemma valid_part44_3 : FiniteIntervals.Covers ValidAt 531 532 :=
  FiniteIntervals.of_fin 531 1 valid_sub44_3
lemma valid_sub44_4 : ∀ i : Fin 1, ValidAt (532 + i.val) := by decide +kernel
lemma valid_part44_4 : FiniteIntervals.Covers ValidAt 532 533 :=
  FiniteIntervals.of_fin 532 1 valid_sub44_4
lemma valid_sub44_5 : ∀ i : Fin 1, ValidAt (533 + i.val) := by decide +kernel
lemma valid_part44_5 : FiniteIntervals.Covers ValidAt 533 534 :=
  FiniteIntervals.of_fin 533 1 valid_sub44_5
lemma valid_sub44_6 : ∀ i : Fin 1, ValidAt (534 + i.val) := by decide +kernel
lemma valid_part44_6 : FiniteIntervals.Covers ValidAt 534 535 :=
  FiniteIntervals.of_fin 534 1 valid_sub44_6
lemma valid_sub44_7 : ∀ i : Fin 1, ValidAt (535 + i.val) := by decide +kernel
lemma valid_part44_7 : FiniteIntervals.Covers ValidAt 535 536 :=
  FiniteIntervals.of_fin 535 1 valid_sub44_7
lemma valid_sub44_8 : ∀ i : Fin 1, ValidAt (536 + i.val) := by decide +kernel
lemma valid_part44_8 : FiniteIntervals.Covers ValidAt 536 537 :=
  FiniteIntervals.of_fin 536 1 valid_sub44_8
lemma valid_sub44_9 : ∀ i : Fin 1, ValidAt (537 + i.val) := by decide +kernel
lemma valid_part44_9 : FiniteIntervals.Covers ValidAt 537 538 :=
  FiniteIntervals.of_fin 537 1 valid_sub44_9
lemma valid_sub44_10 : ∀ i : Fin 1, ValidAt (538 + i.val) := by decide +kernel
lemma valid_part44_10 : FiniteIntervals.Covers ValidAt 538 539 :=
  FiniteIntervals.of_fin 538 1 valid_sub44_10
lemma valid_sub44_11 : ∀ i : Fin 1, ValidAt (539 + i.val) := by decide +kernel
lemma valid_part44_11 : FiniteIntervals.Covers ValidAt 539 540 :=
  FiniteIntervals.of_fin 539 1 valid_sub44_11
lemma valid_interval44 : FiniteIntervals.Covers ValidAt 528 540 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part44_0 (FiniteIntervals.merge valid_part44_1 valid_part44_2)) (FiniteIntervals.merge valid_part44_3 (FiniteIntervals.merge valid_part44_4 valid_part44_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part44_6 (FiniteIntervals.merge valid_part44_7 valid_part44_8)) (FiniteIntervals.merge valid_part44_9 (FiniteIntervals.merge valid_part44_10 valid_part44_11))))
#print axioms valid_interval44
end Erdos184Work.PureSixActions0
