import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub8_0 : ∀ i : Fin 1, ValidAt (64 + i.val) := by decide +kernel
lemma valid_part8_0 : FiniteIntervals.Covers ValidAt 64 65 :=
  FiniteIntervals.of_fin 64 1 valid_sub8_0
lemma valid_sub8_1 : ∀ i : Fin 1, ValidAt (65 + i.val) := by decide +kernel
lemma valid_part8_1 : FiniteIntervals.Covers ValidAt 65 66 :=
  FiniteIntervals.of_fin 65 1 valid_sub8_1
lemma valid_sub8_2 : ∀ i : Fin 1, ValidAt (66 + i.val) := by decide +kernel
lemma valid_part8_2 : FiniteIntervals.Covers ValidAt 66 67 :=
  FiniteIntervals.of_fin 66 1 valid_sub8_2
lemma valid_sub8_3 : ∀ i : Fin 1, ValidAt (67 + i.val) := by decide +kernel
lemma valid_part8_3 : FiniteIntervals.Covers ValidAt 67 68 :=
  FiniteIntervals.of_fin 67 1 valid_sub8_3
lemma valid_sub8_4 : ∀ i : Fin 1, ValidAt (68 + i.val) := by decide +kernel
lemma valid_part8_4 : FiniteIntervals.Covers ValidAt 68 69 :=
  FiniteIntervals.of_fin 68 1 valid_sub8_4
lemma valid_sub8_5 : ∀ i : Fin 1, ValidAt (69 + i.val) := by decide +kernel
lemma valid_part8_5 : FiniteIntervals.Covers ValidAt 69 70 :=
  FiniteIntervals.of_fin 69 1 valid_sub8_5
lemma valid_sub8_6 : ∀ i : Fin 1, ValidAt (70 + i.val) := by decide +kernel
lemma valid_part8_6 : FiniteIntervals.Covers ValidAt 70 71 :=
  FiniteIntervals.of_fin 70 1 valid_sub8_6
lemma valid_sub8_7 : ∀ i : Fin 1, ValidAt (71 + i.val) := by decide +kernel
lemma valid_part8_7 : FiniteIntervals.Covers ValidAt 71 72 :=
  FiniteIntervals.of_fin 71 1 valid_sub8_7
lemma valid_interval8 : FiniteIntervals.Covers ValidAt 64 72 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part8_0 valid_part8_1) (FiniteIntervals.merge valid_part8_2 valid_part8_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part8_4 valid_part8_5) (FiniteIntervals.merge valid_part8_6 valid_part8_7)))
#print axioms valid_interval8
end Erdos184Work.PureSixActions1
