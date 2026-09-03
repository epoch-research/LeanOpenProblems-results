import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub46_0 : ∀ i : Fin 1, ValidAt (552 + i.val) := by decide +kernel
lemma valid_part46_0 : FiniteIntervals.Covers ValidAt 552 553 :=
  FiniteIntervals.of_fin 552 1 valid_sub46_0
lemma valid_sub46_1 : ∀ i : Fin 1, ValidAt (553 + i.val) := by decide +kernel
lemma valid_part46_1 : FiniteIntervals.Covers ValidAt 553 554 :=
  FiniteIntervals.of_fin 553 1 valid_sub46_1
lemma valid_sub46_2 : ∀ i : Fin 1, ValidAt (554 + i.val) := by decide +kernel
lemma valid_part46_2 : FiniteIntervals.Covers ValidAt 554 555 :=
  FiniteIntervals.of_fin 554 1 valid_sub46_2
lemma valid_sub46_3 : ∀ i : Fin 1, ValidAt (555 + i.val) := by decide +kernel
lemma valid_part46_3 : FiniteIntervals.Covers ValidAt 555 556 :=
  FiniteIntervals.of_fin 555 1 valid_sub46_3
lemma valid_sub46_4 : ∀ i : Fin 1, ValidAt (556 + i.val) := by decide +kernel
lemma valid_part46_4 : FiniteIntervals.Covers ValidAt 556 557 :=
  FiniteIntervals.of_fin 556 1 valid_sub46_4
lemma valid_sub46_5 : ∀ i : Fin 1, ValidAt (557 + i.val) := by decide +kernel
lemma valid_part46_5 : FiniteIntervals.Covers ValidAt 557 558 :=
  FiniteIntervals.of_fin 557 1 valid_sub46_5
lemma valid_sub46_6 : ∀ i : Fin 1, ValidAt (558 + i.val) := by decide +kernel
lemma valid_part46_6 : FiniteIntervals.Covers ValidAt 558 559 :=
  FiniteIntervals.of_fin 558 1 valid_sub46_6
lemma valid_sub46_7 : ∀ i : Fin 1, ValidAt (559 + i.val) := by decide +kernel
lemma valid_part46_7 : FiniteIntervals.Covers ValidAt 559 560 :=
  FiniteIntervals.of_fin 559 1 valid_sub46_7
lemma valid_sub46_8 : ∀ i : Fin 1, ValidAt (560 + i.val) := by decide +kernel
lemma valid_part46_8 : FiniteIntervals.Covers ValidAt 560 561 :=
  FiniteIntervals.of_fin 560 1 valid_sub46_8
lemma valid_sub46_9 : ∀ i : Fin 1, ValidAt (561 + i.val) := by decide +kernel
lemma valid_part46_9 : FiniteIntervals.Covers ValidAt 561 562 :=
  FiniteIntervals.of_fin 561 1 valid_sub46_9
lemma valid_sub46_10 : ∀ i : Fin 1, ValidAt (562 + i.val) := by decide +kernel
lemma valid_part46_10 : FiniteIntervals.Covers ValidAt 562 563 :=
  FiniteIntervals.of_fin 562 1 valid_sub46_10
lemma valid_sub46_11 : ∀ i : Fin 1, ValidAt (563 + i.val) := by decide +kernel
lemma valid_part46_11 : FiniteIntervals.Covers ValidAt 563 564 :=
  FiniteIntervals.of_fin 563 1 valid_sub46_11
lemma valid_interval46 : FiniteIntervals.Covers ValidAt 552 564 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part46_0 (FiniteIntervals.merge valid_part46_1 valid_part46_2)) (FiniteIntervals.merge valid_part46_3 (FiniteIntervals.merge valid_part46_4 valid_part46_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part46_6 (FiniteIntervals.merge valid_part46_7 valid_part46_8)) (FiniteIntervals.merge valid_part46_9 (FiniteIntervals.merge valid_part46_10 valid_part46_11))))
#print axioms valid_interval46
end Erdos184Work.PureSixActions0
