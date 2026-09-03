import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub41_0 : ∀ i : Fin 1, ValidAt (492 + i.val) := by decide +kernel
lemma valid_part41_0 : FiniteIntervals.Covers ValidAt 492 493 :=
  FiniteIntervals.of_fin 492 1 valid_sub41_0
lemma valid_sub41_1 : ∀ i : Fin 1, ValidAt (493 + i.val) := by decide +kernel
lemma valid_part41_1 : FiniteIntervals.Covers ValidAt 493 494 :=
  FiniteIntervals.of_fin 493 1 valid_sub41_1
lemma valid_sub41_2 : ∀ i : Fin 1, ValidAt (494 + i.val) := by decide +kernel
lemma valid_part41_2 : FiniteIntervals.Covers ValidAt 494 495 :=
  FiniteIntervals.of_fin 494 1 valid_sub41_2
lemma valid_sub41_3 : ∀ i : Fin 1, ValidAt (495 + i.val) := by decide +kernel
lemma valid_part41_3 : FiniteIntervals.Covers ValidAt 495 496 :=
  FiniteIntervals.of_fin 495 1 valid_sub41_3
lemma valid_sub41_4 : ∀ i : Fin 1, ValidAt (496 + i.val) := by decide +kernel
lemma valid_part41_4 : FiniteIntervals.Covers ValidAt 496 497 :=
  FiniteIntervals.of_fin 496 1 valid_sub41_4
lemma valid_sub41_5 : ∀ i : Fin 1, ValidAt (497 + i.val) := by decide +kernel
lemma valid_part41_5 : FiniteIntervals.Covers ValidAt 497 498 :=
  FiniteIntervals.of_fin 497 1 valid_sub41_5
lemma valid_sub41_6 : ∀ i : Fin 1, ValidAt (498 + i.val) := by decide +kernel
lemma valid_part41_6 : FiniteIntervals.Covers ValidAt 498 499 :=
  FiniteIntervals.of_fin 498 1 valid_sub41_6
lemma valid_sub41_7 : ∀ i : Fin 1, ValidAt (499 + i.val) := by decide +kernel
lemma valid_part41_7 : FiniteIntervals.Covers ValidAt 499 500 :=
  FiniteIntervals.of_fin 499 1 valid_sub41_7
lemma valid_sub41_8 : ∀ i : Fin 1, ValidAt (500 + i.val) := by decide +kernel
lemma valid_part41_8 : FiniteIntervals.Covers ValidAt 500 501 :=
  FiniteIntervals.of_fin 500 1 valid_sub41_8
lemma valid_sub41_9 : ∀ i : Fin 1, ValidAt (501 + i.val) := by decide +kernel
lemma valid_part41_9 : FiniteIntervals.Covers ValidAt 501 502 :=
  FiniteIntervals.of_fin 501 1 valid_sub41_9
lemma valid_sub41_10 : ∀ i : Fin 1, ValidAt (502 + i.val) := by decide +kernel
lemma valid_part41_10 : FiniteIntervals.Covers ValidAt 502 503 :=
  FiniteIntervals.of_fin 502 1 valid_sub41_10
lemma valid_sub41_11 : ∀ i : Fin 1, ValidAt (503 + i.val) := by decide +kernel
lemma valid_part41_11 : FiniteIntervals.Covers ValidAt 503 504 :=
  FiniteIntervals.of_fin 503 1 valid_sub41_11
lemma valid_interval41 : FiniteIntervals.Covers ValidAt 492 504 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part41_0 (FiniteIntervals.merge valid_part41_1 valid_part41_2)) (FiniteIntervals.merge valid_part41_3 (FiniteIntervals.merge valid_part41_4 valid_part41_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part41_6 (FiniteIntervals.merge valid_part41_7 valid_part41_8)) (FiniteIntervals.merge valid_part41_9 (FiniteIntervals.merge valid_part41_10 valid_part41_11))))
#print axioms valid_interval41
end Erdos184Work.PureSixActions0
