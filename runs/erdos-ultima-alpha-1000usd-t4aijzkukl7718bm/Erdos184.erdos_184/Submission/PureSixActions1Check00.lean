import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub0_0 : ∀ i : Fin 1, ValidAt (0 + i.val) := by decide +kernel
lemma valid_part0_0 : FiniteIntervals.Covers ValidAt 0 1 :=
  FiniteIntervals.of_fin 0 1 valid_sub0_0
lemma valid_sub0_1 : ∀ i : Fin 1, ValidAt (1 + i.val) := by decide +kernel
lemma valid_part0_1 : FiniteIntervals.Covers ValidAt 1 2 :=
  FiniteIntervals.of_fin 1 1 valid_sub0_1
lemma valid_sub0_2 : ∀ i : Fin 1, ValidAt (2 + i.val) := by decide +kernel
lemma valid_part0_2 : FiniteIntervals.Covers ValidAt 2 3 :=
  FiniteIntervals.of_fin 2 1 valid_sub0_2
lemma valid_sub0_3 : ∀ i : Fin 1, ValidAt (3 + i.val) := by decide +kernel
lemma valid_part0_3 : FiniteIntervals.Covers ValidAt 3 4 :=
  FiniteIntervals.of_fin 3 1 valid_sub0_3
lemma valid_sub0_4 : ∀ i : Fin 1, ValidAt (4 + i.val) := by decide +kernel
lemma valid_part0_4 : FiniteIntervals.Covers ValidAt 4 5 :=
  FiniteIntervals.of_fin 4 1 valid_sub0_4
lemma valid_sub0_5 : ∀ i : Fin 1, ValidAt (5 + i.val) := by decide +kernel
lemma valid_part0_5 : FiniteIntervals.Covers ValidAt 5 6 :=
  FiniteIntervals.of_fin 5 1 valid_sub0_5
lemma valid_sub0_6 : ∀ i : Fin 1, ValidAt (6 + i.val) := by decide +kernel
lemma valid_part0_6 : FiniteIntervals.Covers ValidAt 6 7 :=
  FiniteIntervals.of_fin 6 1 valid_sub0_6
lemma valid_sub0_7 : ∀ i : Fin 1, ValidAt (7 + i.val) := by decide +kernel
lemma valid_part0_7 : FiniteIntervals.Covers ValidAt 7 8 :=
  FiniteIntervals.of_fin 7 1 valid_sub0_7
lemma valid_interval0 : FiniteIntervals.Covers ValidAt 0 8 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part0_0 valid_part0_1) (FiniteIntervals.merge valid_part0_2 valid_part0_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part0_4 valid_part0_5) (FiniteIntervals.merge valid_part0_6 valid_part0_7)))
#print axioms valid_interval0
end Erdos184Work.PureSixActions1
