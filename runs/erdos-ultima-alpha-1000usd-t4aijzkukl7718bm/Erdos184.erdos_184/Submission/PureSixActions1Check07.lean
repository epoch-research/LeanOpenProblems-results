import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub7_0 : ∀ i : Fin 1, ValidAt (56 + i.val) := by decide +kernel
lemma valid_part7_0 : FiniteIntervals.Covers ValidAt 56 57 :=
  FiniteIntervals.of_fin 56 1 valid_sub7_0
lemma valid_sub7_1 : ∀ i : Fin 1, ValidAt (57 + i.val) := by decide +kernel
lemma valid_part7_1 : FiniteIntervals.Covers ValidAt 57 58 :=
  FiniteIntervals.of_fin 57 1 valid_sub7_1
lemma valid_sub7_2 : ∀ i : Fin 1, ValidAt (58 + i.val) := by decide +kernel
lemma valid_part7_2 : FiniteIntervals.Covers ValidAt 58 59 :=
  FiniteIntervals.of_fin 58 1 valid_sub7_2
lemma valid_sub7_3 : ∀ i : Fin 1, ValidAt (59 + i.val) := by decide +kernel
lemma valid_part7_3 : FiniteIntervals.Covers ValidAt 59 60 :=
  FiniteIntervals.of_fin 59 1 valid_sub7_3
lemma valid_sub7_4 : ∀ i : Fin 1, ValidAt (60 + i.val) := by decide +kernel
lemma valid_part7_4 : FiniteIntervals.Covers ValidAt 60 61 :=
  FiniteIntervals.of_fin 60 1 valid_sub7_4
lemma valid_sub7_5 : ∀ i : Fin 1, ValidAt (61 + i.val) := by decide +kernel
lemma valid_part7_5 : FiniteIntervals.Covers ValidAt 61 62 :=
  FiniteIntervals.of_fin 61 1 valid_sub7_5
lemma valid_sub7_6 : ∀ i : Fin 1, ValidAt (62 + i.val) := by decide +kernel
lemma valid_part7_6 : FiniteIntervals.Covers ValidAt 62 63 :=
  FiniteIntervals.of_fin 62 1 valid_sub7_6
lemma valid_sub7_7 : ∀ i : Fin 1, ValidAt (63 + i.val) := by decide +kernel
lemma valid_part7_7 : FiniteIntervals.Covers ValidAt 63 64 :=
  FiniteIntervals.of_fin 63 1 valid_sub7_7
lemma valid_interval7 : FiniteIntervals.Covers ValidAt 56 64 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part7_0 valid_part7_1) (FiniteIntervals.merge valid_part7_2 valid_part7_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part7_4 valid_part7_5) (FiniteIntervals.merge valid_part7_6 valid_part7_7)))
#print axioms valid_interval7
end Erdos184Work.PureSixActions1
