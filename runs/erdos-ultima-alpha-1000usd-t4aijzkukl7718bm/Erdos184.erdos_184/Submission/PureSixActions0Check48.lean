import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub48_0 : ∀ i : Fin 1, ValidAt (576 + i.val) := by decide +kernel
lemma valid_part48_0 : FiniteIntervals.Covers ValidAt 576 577 :=
  FiniteIntervals.of_fin 576 1 valid_sub48_0
lemma valid_sub48_1 : ∀ i : Fin 1, ValidAt (577 + i.val) := by decide +kernel
lemma valid_part48_1 : FiniteIntervals.Covers ValidAt 577 578 :=
  FiniteIntervals.of_fin 577 1 valid_sub48_1
lemma valid_sub48_2 : ∀ i : Fin 1, ValidAt (578 + i.val) := by decide +kernel
lemma valid_part48_2 : FiniteIntervals.Covers ValidAt 578 579 :=
  FiniteIntervals.of_fin 578 1 valid_sub48_2
lemma valid_sub48_3 : ∀ i : Fin 1, ValidAt (579 + i.val) := by decide +kernel
lemma valid_part48_3 : FiniteIntervals.Covers ValidAt 579 580 :=
  FiniteIntervals.of_fin 579 1 valid_sub48_3
lemma valid_sub48_4 : ∀ i : Fin 1, ValidAt (580 + i.val) := by decide +kernel
lemma valid_part48_4 : FiniteIntervals.Covers ValidAt 580 581 :=
  FiniteIntervals.of_fin 580 1 valid_sub48_4
lemma valid_sub48_5 : ∀ i : Fin 1, ValidAt (581 + i.val) := by decide +kernel
lemma valid_part48_5 : FiniteIntervals.Covers ValidAt 581 582 :=
  FiniteIntervals.of_fin 581 1 valid_sub48_5
lemma valid_sub48_6 : ∀ i : Fin 1, ValidAt (582 + i.val) := by decide +kernel
lemma valid_part48_6 : FiniteIntervals.Covers ValidAt 582 583 :=
  FiniteIntervals.of_fin 582 1 valid_sub48_6
lemma valid_sub48_7 : ∀ i : Fin 1, ValidAt (583 + i.val) := by decide +kernel
lemma valid_part48_7 : FiniteIntervals.Covers ValidAt 583 584 :=
  FiniteIntervals.of_fin 583 1 valid_sub48_7
lemma valid_sub48_8 : ∀ i : Fin 1, ValidAt (584 + i.val) := by decide +kernel
lemma valid_part48_8 : FiniteIntervals.Covers ValidAt 584 585 :=
  FiniteIntervals.of_fin 584 1 valid_sub48_8
lemma valid_sub48_9 : ∀ i : Fin 1, ValidAt (585 + i.val) := by decide +kernel
lemma valid_part48_9 : FiniteIntervals.Covers ValidAt 585 586 :=
  FiniteIntervals.of_fin 585 1 valid_sub48_9
lemma valid_sub48_10 : ∀ i : Fin 1, ValidAt (586 + i.val) := by decide +kernel
lemma valid_part48_10 : FiniteIntervals.Covers ValidAt 586 587 :=
  FiniteIntervals.of_fin 586 1 valid_sub48_10
lemma valid_sub48_11 : ∀ i : Fin 1, ValidAt (587 + i.val) := by decide +kernel
lemma valid_part48_11 : FiniteIntervals.Covers ValidAt 587 588 :=
  FiniteIntervals.of_fin 587 1 valid_sub48_11
lemma valid_interval48 : FiniteIntervals.Covers ValidAt 576 588 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part48_0 (FiniteIntervals.merge valid_part48_1 valid_part48_2)) (FiniteIntervals.merge valid_part48_3 (FiniteIntervals.merge valid_part48_4 valid_part48_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part48_6 (FiniteIntervals.merge valid_part48_7 valid_part48_8)) (FiniteIntervals.merge valid_part48_9 (FiniteIntervals.merge valid_part48_10 valid_part48_11))))
#print axioms valid_interval48
end Erdos184Work.PureSixActions0
