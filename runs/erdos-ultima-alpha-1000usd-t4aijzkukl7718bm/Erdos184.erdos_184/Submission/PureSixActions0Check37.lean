import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub37_0 : ∀ i : Fin 1, ValidAt (444 + i.val) := by decide +kernel
lemma valid_part37_0 : FiniteIntervals.Covers ValidAt 444 445 :=
  FiniteIntervals.of_fin 444 1 valid_sub37_0
lemma valid_sub37_1 : ∀ i : Fin 1, ValidAt (445 + i.val) := by decide +kernel
lemma valid_part37_1 : FiniteIntervals.Covers ValidAt 445 446 :=
  FiniteIntervals.of_fin 445 1 valid_sub37_1
lemma valid_sub37_2 : ∀ i : Fin 1, ValidAt (446 + i.val) := by decide +kernel
lemma valid_part37_2 : FiniteIntervals.Covers ValidAt 446 447 :=
  FiniteIntervals.of_fin 446 1 valid_sub37_2
lemma valid_sub37_3 : ∀ i : Fin 1, ValidAt (447 + i.val) := by decide +kernel
lemma valid_part37_3 : FiniteIntervals.Covers ValidAt 447 448 :=
  FiniteIntervals.of_fin 447 1 valid_sub37_3
lemma valid_sub37_4 : ∀ i : Fin 1, ValidAt (448 + i.val) := by decide +kernel
lemma valid_part37_4 : FiniteIntervals.Covers ValidAt 448 449 :=
  FiniteIntervals.of_fin 448 1 valid_sub37_4
lemma valid_sub37_5 : ∀ i : Fin 1, ValidAt (449 + i.val) := by decide +kernel
lemma valid_part37_5 : FiniteIntervals.Covers ValidAt 449 450 :=
  FiniteIntervals.of_fin 449 1 valid_sub37_5
lemma valid_sub37_6 : ∀ i : Fin 1, ValidAt (450 + i.val) := by decide +kernel
lemma valid_part37_6 : FiniteIntervals.Covers ValidAt 450 451 :=
  FiniteIntervals.of_fin 450 1 valid_sub37_6
lemma valid_sub37_7 : ∀ i : Fin 1, ValidAt (451 + i.val) := by decide +kernel
lemma valid_part37_7 : FiniteIntervals.Covers ValidAt 451 452 :=
  FiniteIntervals.of_fin 451 1 valid_sub37_7
lemma valid_sub37_8 : ∀ i : Fin 1, ValidAt (452 + i.val) := by decide +kernel
lemma valid_part37_8 : FiniteIntervals.Covers ValidAt 452 453 :=
  FiniteIntervals.of_fin 452 1 valid_sub37_8
lemma valid_sub37_9 : ∀ i : Fin 1, ValidAt (453 + i.val) := by decide +kernel
lemma valid_part37_9 : FiniteIntervals.Covers ValidAt 453 454 :=
  FiniteIntervals.of_fin 453 1 valid_sub37_9
lemma valid_sub37_10 : ∀ i : Fin 1, ValidAt (454 + i.val) := by decide +kernel
lemma valid_part37_10 : FiniteIntervals.Covers ValidAt 454 455 :=
  FiniteIntervals.of_fin 454 1 valid_sub37_10
lemma valid_sub37_11 : ∀ i : Fin 1, ValidAt (455 + i.val) := by decide +kernel
lemma valid_part37_11 : FiniteIntervals.Covers ValidAt 455 456 :=
  FiniteIntervals.of_fin 455 1 valid_sub37_11
lemma valid_interval37 : FiniteIntervals.Covers ValidAt 444 456 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part37_0 (FiniteIntervals.merge valid_part37_1 valid_part37_2)) (FiniteIntervals.merge valid_part37_3 (FiniteIntervals.merge valid_part37_4 valid_part37_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part37_6 (FiniteIntervals.merge valid_part37_7 valid_part37_8)) (FiniteIntervals.merge valid_part37_9 (FiniteIntervals.merge valid_part37_10 valid_part37_11))))
#print axioms valid_interval37
end Erdos184Work.PureSixActions0
