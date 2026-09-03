import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub10_0 : ∀ i : Fin 1, ValidAt (80 + i.val) := by decide +kernel
lemma valid_part10_0 : FiniteIntervals.Covers ValidAt 80 81 :=
  FiniteIntervals.of_fin 80 1 valid_sub10_0
lemma valid_sub10_1 : ∀ i : Fin 1, ValidAt (81 + i.val) := by decide +kernel
lemma valid_part10_1 : FiniteIntervals.Covers ValidAt 81 82 :=
  FiniteIntervals.of_fin 81 1 valid_sub10_1
lemma valid_sub10_2 : ∀ i : Fin 1, ValidAt (82 + i.val) := by decide +kernel
lemma valid_part10_2 : FiniteIntervals.Covers ValidAt 82 83 :=
  FiniteIntervals.of_fin 82 1 valid_sub10_2
lemma valid_sub10_3 : ∀ i : Fin 1, ValidAt (83 + i.val) := by decide +kernel
lemma valid_part10_3 : FiniteIntervals.Covers ValidAt 83 84 :=
  FiniteIntervals.of_fin 83 1 valid_sub10_3
lemma valid_sub10_4 : ∀ i : Fin 1, ValidAt (84 + i.val) := by decide +kernel
lemma valid_part10_4 : FiniteIntervals.Covers ValidAt 84 85 :=
  FiniteIntervals.of_fin 84 1 valid_sub10_4
lemma valid_sub10_5 : ∀ i : Fin 1, ValidAt (85 + i.val) := by decide +kernel
lemma valid_part10_5 : FiniteIntervals.Covers ValidAt 85 86 :=
  FiniteIntervals.of_fin 85 1 valid_sub10_5
lemma valid_sub10_6 : ∀ i : Fin 1, ValidAt (86 + i.val) := by decide +kernel
lemma valid_part10_6 : FiniteIntervals.Covers ValidAt 86 87 :=
  FiniteIntervals.of_fin 86 1 valid_sub10_6
lemma valid_sub10_7 : ∀ i : Fin 1, ValidAt (87 + i.val) := by decide +kernel
lemma valid_part10_7 : FiniteIntervals.Covers ValidAt 87 88 :=
  FiniteIntervals.of_fin 87 1 valid_sub10_7
lemma valid_interval10 : FiniteIntervals.Covers ValidAt 80 88 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part10_0 valid_part10_1) (FiniteIntervals.merge valid_part10_2 valid_part10_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part10_4 valid_part10_5) (FiniteIntervals.merge valid_part10_6 valid_part10_7)))
#print axioms valid_interval10
end Erdos184Work.PureSixActions1
