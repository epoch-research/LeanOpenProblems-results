import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub3_0 : ∀ i : Fin 1, ValidAt (24 + i.val) := by decide +kernel
lemma valid_part3_0 : FiniteIntervals.Covers ValidAt 24 25 :=
  FiniteIntervals.of_fin 24 1 valid_sub3_0
lemma valid_sub3_1 : ∀ i : Fin 1, ValidAt (25 + i.val) := by decide +kernel
lemma valid_part3_1 : FiniteIntervals.Covers ValidAt 25 26 :=
  FiniteIntervals.of_fin 25 1 valid_sub3_1
lemma valid_sub3_2 : ∀ i : Fin 1, ValidAt (26 + i.val) := by decide +kernel
lemma valid_part3_2 : FiniteIntervals.Covers ValidAt 26 27 :=
  FiniteIntervals.of_fin 26 1 valid_sub3_2
lemma valid_sub3_3 : ∀ i : Fin 1, ValidAt (27 + i.val) := by decide +kernel
lemma valid_part3_3 : FiniteIntervals.Covers ValidAt 27 28 :=
  FiniteIntervals.of_fin 27 1 valid_sub3_3
lemma valid_sub3_4 : ∀ i : Fin 1, ValidAt (28 + i.val) := by decide +kernel
lemma valid_part3_4 : FiniteIntervals.Covers ValidAt 28 29 :=
  FiniteIntervals.of_fin 28 1 valid_sub3_4
lemma valid_sub3_5 : ∀ i : Fin 1, ValidAt (29 + i.val) := by decide +kernel
lemma valid_part3_5 : FiniteIntervals.Covers ValidAt 29 30 :=
  FiniteIntervals.of_fin 29 1 valid_sub3_5
lemma valid_sub3_6 : ∀ i : Fin 1, ValidAt (30 + i.val) := by decide +kernel
lemma valid_part3_6 : FiniteIntervals.Covers ValidAt 30 31 :=
  FiniteIntervals.of_fin 30 1 valid_sub3_6
lemma valid_sub3_7 : ∀ i : Fin 1, ValidAt (31 + i.val) := by decide +kernel
lemma valid_part3_7 : FiniteIntervals.Covers ValidAt 31 32 :=
  FiniteIntervals.of_fin 31 1 valid_sub3_7
lemma valid_interval3 : FiniteIntervals.Covers ValidAt 24 32 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part3_0 valid_part3_1) (FiniteIntervals.merge valid_part3_2 valid_part3_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part3_4 valid_part3_5) (FiniteIntervals.merge valid_part3_6 valid_part3_7)))
#print axioms valid_interval3
end Erdos184Work.PureSixActions1
