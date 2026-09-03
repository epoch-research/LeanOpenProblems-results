import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub2_0 : ∀ i : Fin 1, ValidAt (16 + i.val) := by decide +kernel
lemma valid_part2_0 : FiniteIntervals.Covers ValidAt 16 17 :=
  FiniteIntervals.of_fin 16 1 valid_sub2_0
lemma valid_sub2_1 : ∀ i : Fin 1, ValidAt (17 + i.val) := by decide +kernel
lemma valid_part2_1 : FiniteIntervals.Covers ValidAt 17 18 :=
  FiniteIntervals.of_fin 17 1 valid_sub2_1
lemma valid_sub2_2 : ∀ i : Fin 1, ValidAt (18 + i.val) := by decide +kernel
lemma valid_part2_2 : FiniteIntervals.Covers ValidAt 18 19 :=
  FiniteIntervals.of_fin 18 1 valid_sub2_2
lemma valid_sub2_3 : ∀ i : Fin 1, ValidAt (19 + i.val) := by decide +kernel
lemma valid_part2_3 : FiniteIntervals.Covers ValidAt 19 20 :=
  FiniteIntervals.of_fin 19 1 valid_sub2_3
lemma valid_sub2_4 : ∀ i : Fin 1, ValidAt (20 + i.val) := by decide +kernel
lemma valid_part2_4 : FiniteIntervals.Covers ValidAt 20 21 :=
  FiniteIntervals.of_fin 20 1 valid_sub2_4
lemma valid_sub2_5 : ∀ i : Fin 1, ValidAt (21 + i.val) := by decide +kernel
lemma valid_part2_5 : FiniteIntervals.Covers ValidAt 21 22 :=
  FiniteIntervals.of_fin 21 1 valid_sub2_5
lemma valid_sub2_6 : ∀ i : Fin 1, ValidAt (22 + i.val) := by decide +kernel
lemma valid_part2_6 : FiniteIntervals.Covers ValidAt 22 23 :=
  FiniteIntervals.of_fin 22 1 valid_sub2_6
lemma valid_sub2_7 : ∀ i : Fin 1, ValidAt (23 + i.val) := by decide +kernel
lemma valid_part2_7 : FiniteIntervals.Covers ValidAt 23 24 :=
  FiniteIntervals.of_fin 23 1 valid_sub2_7
lemma valid_interval2 : FiniteIntervals.Covers ValidAt 16 24 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part2_0 valid_part2_1) (FiniteIntervals.merge valid_part2_2 valid_part2_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part2_4 valid_part2_5) (FiniteIntervals.merge valid_part2_6 valid_part2_7)))
#print axioms valid_interval2
end Erdos184Work.PureSixActions1
