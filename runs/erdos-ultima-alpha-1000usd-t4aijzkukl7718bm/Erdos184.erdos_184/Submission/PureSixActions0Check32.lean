import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub32_0 : ∀ i : Fin 1, ValidAt (384 + i.val) := by decide +kernel
lemma valid_part32_0 : FiniteIntervals.Covers ValidAt 384 385 :=
  FiniteIntervals.of_fin 384 1 valid_sub32_0
lemma valid_sub32_1 : ∀ i : Fin 1, ValidAt (385 + i.val) := by decide +kernel
lemma valid_part32_1 : FiniteIntervals.Covers ValidAt 385 386 :=
  FiniteIntervals.of_fin 385 1 valid_sub32_1
lemma valid_sub32_2 : ∀ i : Fin 1, ValidAt (386 + i.val) := by decide +kernel
lemma valid_part32_2 : FiniteIntervals.Covers ValidAt 386 387 :=
  FiniteIntervals.of_fin 386 1 valid_sub32_2
lemma valid_sub32_3 : ∀ i : Fin 1, ValidAt (387 + i.val) := by decide +kernel
lemma valid_part32_3 : FiniteIntervals.Covers ValidAt 387 388 :=
  FiniteIntervals.of_fin 387 1 valid_sub32_3
lemma valid_sub32_4 : ∀ i : Fin 1, ValidAt (388 + i.val) := by decide +kernel
lemma valid_part32_4 : FiniteIntervals.Covers ValidAt 388 389 :=
  FiniteIntervals.of_fin 388 1 valid_sub32_4
lemma valid_sub32_5 : ∀ i : Fin 1, ValidAt (389 + i.val) := by decide +kernel
lemma valid_part32_5 : FiniteIntervals.Covers ValidAt 389 390 :=
  FiniteIntervals.of_fin 389 1 valid_sub32_5
lemma valid_sub32_6 : ∀ i : Fin 1, ValidAt (390 + i.val) := by decide +kernel
lemma valid_part32_6 : FiniteIntervals.Covers ValidAt 390 391 :=
  FiniteIntervals.of_fin 390 1 valid_sub32_6
lemma valid_sub32_7 : ∀ i : Fin 1, ValidAt (391 + i.val) := by decide +kernel
lemma valid_part32_7 : FiniteIntervals.Covers ValidAt 391 392 :=
  FiniteIntervals.of_fin 391 1 valid_sub32_7
lemma valid_sub32_8 : ∀ i : Fin 1, ValidAt (392 + i.val) := by decide +kernel
lemma valid_part32_8 : FiniteIntervals.Covers ValidAt 392 393 :=
  FiniteIntervals.of_fin 392 1 valid_sub32_8
lemma valid_sub32_9 : ∀ i : Fin 1, ValidAt (393 + i.val) := by decide +kernel
lemma valid_part32_9 : FiniteIntervals.Covers ValidAt 393 394 :=
  FiniteIntervals.of_fin 393 1 valid_sub32_9
lemma valid_sub32_10 : ∀ i : Fin 1, ValidAt (394 + i.val) := by decide +kernel
lemma valid_part32_10 : FiniteIntervals.Covers ValidAt 394 395 :=
  FiniteIntervals.of_fin 394 1 valid_sub32_10
lemma valid_sub32_11 : ∀ i : Fin 1, ValidAt (395 + i.val) := by decide +kernel
lemma valid_part32_11 : FiniteIntervals.Covers ValidAt 395 396 :=
  FiniteIntervals.of_fin 395 1 valid_sub32_11
lemma valid_interval32 : FiniteIntervals.Covers ValidAt 384 396 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part32_0 (FiniteIntervals.merge valid_part32_1 valid_part32_2)) (FiniteIntervals.merge valid_part32_3 (FiniteIntervals.merge valid_part32_4 valid_part32_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part32_6 (FiniteIntervals.merge valid_part32_7 valid_part32_8)) (FiniteIntervals.merge valid_part32_9 (FiniteIntervals.merge valid_part32_10 valid_part32_11))))
#print axioms valid_interval32
end Erdos184Work.PureSixActions0
