import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub43_0 : ∀ i : Fin 1, ValidAt (516 + i.val) := by decide +kernel
lemma valid_part43_0 : FiniteIntervals.Covers ValidAt 516 517 :=
  FiniteIntervals.of_fin 516 1 valid_sub43_0
lemma valid_sub43_1 : ∀ i : Fin 1, ValidAt (517 + i.val) := by decide +kernel
lemma valid_part43_1 : FiniteIntervals.Covers ValidAt 517 518 :=
  FiniteIntervals.of_fin 517 1 valid_sub43_1
lemma valid_sub43_2 : ∀ i : Fin 1, ValidAt (518 + i.val) := by decide +kernel
lemma valid_part43_2 : FiniteIntervals.Covers ValidAt 518 519 :=
  FiniteIntervals.of_fin 518 1 valid_sub43_2
lemma valid_sub43_3 : ∀ i : Fin 1, ValidAt (519 + i.val) := by decide +kernel
lemma valid_part43_3 : FiniteIntervals.Covers ValidAt 519 520 :=
  FiniteIntervals.of_fin 519 1 valid_sub43_3
lemma valid_sub43_4 : ∀ i : Fin 1, ValidAt (520 + i.val) := by decide +kernel
lemma valid_part43_4 : FiniteIntervals.Covers ValidAt 520 521 :=
  FiniteIntervals.of_fin 520 1 valid_sub43_4
lemma valid_sub43_5 : ∀ i : Fin 1, ValidAt (521 + i.val) := by decide +kernel
lemma valid_part43_5 : FiniteIntervals.Covers ValidAt 521 522 :=
  FiniteIntervals.of_fin 521 1 valid_sub43_5
lemma valid_sub43_6 : ∀ i : Fin 1, ValidAt (522 + i.val) := by decide +kernel
lemma valid_part43_6 : FiniteIntervals.Covers ValidAt 522 523 :=
  FiniteIntervals.of_fin 522 1 valid_sub43_6
lemma valid_sub43_7 : ∀ i : Fin 1, ValidAt (523 + i.val) := by decide +kernel
lemma valid_part43_7 : FiniteIntervals.Covers ValidAt 523 524 :=
  FiniteIntervals.of_fin 523 1 valid_sub43_7
lemma valid_sub43_8 : ∀ i : Fin 1, ValidAt (524 + i.val) := by decide +kernel
lemma valid_part43_8 : FiniteIntervals.Covers ValidAt 524 525 :=
  FiniteIntervals.of_fin 524 1 valid_sub43_8
lemma valid_sub43_9 : ∀ i : Fin 1, ValidAt (525 + i.val) := by decide +kernel
lemma valid_part43_9 : FiniteIntervals.Covers ValidAt 525 526 :=
  FiniteIntervals.of_fin 525 1 valid_sub43_9
lemma valid_sub43_10 : ∀ i : Fin 1, ValidAt (526 + i.val) := by decide +kernel
lemma valid_part43_10 : FiniteIntervals.Covers ValidAt 526 527 :=
  FiniteIntervals.of_fin 526 1 valid_sub43_10
lemma valid_sub43_11 : ∀ i : Fin 1, ValidAt (527 + i.val) := by decide +kernel
lemma valid_part43_11 : FiniteIntervals.Covers ValidAt 527 528 :=
  FiniteIntervals.of_fin 527 1 valid_sub43_11
lemma valid_interval43 : FiniteIntervals.Covers ValidAt 516 528 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part43_0 (FiniteIntervals.merge valid_part43_1 valid_part43_2)) (FiniteIntervals.merge valid_part43_3 (FiniteIntervals.merge valid_part43_4 valid_part43_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part43_6 (FiniteIntervals.merge valid_part43_7 valid_part43_8)) (FiniteIntervals.merge valid_part43_9 (FiniteIntervals.merge valid_part43_10 valid_part43_11))))
#print axioms valid_interval43
end Erdos184Work.PureSixActions0
