import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub35_0 : ∀ i : Fin 1, ValidAt (420 + i.val) := by decide +kernel
lemma valid_part35_0 : FiniteIntervals.Covers ValidAt 420 421 :=
  FiniteIntervals.of_fin 420 1 valid_sub35_0
lemma valid_sub35_1 : ∀ i : Fin 1, ValidAt (421 + i.val) := by decide +kernel
lemma valid_part35_1 : FiniteIntervals.Covers ValidAt 421 422 :=
  FiniteIntervals.of_fin 421 1 valid_sub35_1
lemma valid_sub35_2 : ∀ i : Fin 1, ValidAt (422 + i.val) := by decide +kernel
lemma valid_part35_2 : FiniteIntervals.Covers ValidAt 422 423 :=
  FiniteIntervals.of_fin 422 1 valid_sub35_2
lemma valid_sub35_3 : ∀ i : Fin 1, ValidAt (423 + i.val) := by decide +kernel
lemma valid_part35_3 : FiniteIntervals.Covers ValidAt 423 424 :=
  FiniteIntervals.of_fin 423 1 valid_sub35_3
lemma valid_sub35_4 : ∀ i : Fin 1, ValidAt (424 + i.val) := by decide +kernel
lemma valid_part35_4 : FiniteIntervals.Covers ValidAt 424 425 :=
  FiniteIntervals.of_fin 424 1 valid_sub35_4
lemma valid_sub35_5 : ∀ i : Fin 1, ValidAt (425 + i.val) := by decide +kernel
lemma valid_part35_5 : FiniteIntervals.Covers ValidAt 425 426 :=
  FiniteIntervals.of_fin 425 1 valid_sub35_5
lemma valid_sub35_6 : ∀ i : Fin 1, ValidAt (426 + i.val) := by decide +kernel
lemma valid_part35_6 : FiniteIntervals.Covers ValidAt 426 427 :=
  FiniteIntervals.of_fin 426 1 valid_sub35_6
lemma valid_sub35_7 : ∀ i : Fin 1, ValidAt (427 + i.val) := by decide +kernel
lemma valid_part35_7 : FiniteIntervals.Covers ValidAt 427 428 :=
  FiniteIntervals.of_fin 427 1 valid_sub35_7
lemma valid_sub35_8 : ∀ i : Fin 1, ValidAt (428 + i.val) := by decide +kernel
lemma valid_part35_8 : FiniteIntervals.Covers ValidAt 428 429 :=
  FiniteIntervals.of_fin 428 1 valid_sub35_8
lemma valid_sub35_9 : ∀ i : Fin 1, ValidAt (429 + i.val) := by decide +kernel
lemma valid_part35_9 : FiniteIntervals.Covers ValidAt 429 430 :=
  FiniteIntervals.of_fin 429 1 valid_sub35_9
lemma valid_sub35_10 : ∀ i : Fin 1, ValidAt (430 + i.val) := by decide +kernel
lemma valid_part35_10 : FiniteIntervals.Covers ValidAt 430 431 :=
  FiniteIntervals.of_fin 430 1 valid_sub35_10
lemma valid_sub35_11 : ∀ i : Fin 1, ValidAt (431 + i.val) := by decide +kernel
lemma valid_part35_11 : FiniteIntervals.Covers ValidAt 431 432 :=
  FiniteIntervals.of_fin 431 1 valid_sub35_11
lemma valid_interval35 : FiniteIntervals.Covers ValidAt 420 432 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part35_0 (FiniteIntervals.merge valid_part35_1 valid_part35_2)) (FiniteIntervals.merge valid_part35_3 (FiniteIntervals.merge valid_part35_4 valid_part35_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part35_6 (FiniteIntervals.merge valid_part35_7 valid_part35_8)) (FiniteIntervals.merge valid_part35_9 (FiniteIntervals.merge valid_part35_10 valid_part35_11))))
#print axioms valid_interval35
end Erdos184Work.PureSixActions0
