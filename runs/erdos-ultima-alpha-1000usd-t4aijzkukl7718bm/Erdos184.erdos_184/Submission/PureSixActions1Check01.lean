import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub1_0 : ∀ i : Fin 1, ValidAt (8 + i.val) := by decide +kernel
lemma valid_part1_0 : FiniteIntervals.Covers ValidAt 8 9 :=
  FiniteIntervals.of_fin 8 1 valid_sub1_0
lemma valid_sub1_1 : ∀ i : Fin 1, ValidAt (9 + i.val) := by decide +kernel
lemma valid_part1_1 : FiniteIntervals.Covers ValidAt 9 10 :=
  FiniteIntervals.of_fin 9 1 valid_sub1_1
lemma valid_sub1_2 : ∀ i : Fin 1, ValidAt (10 + i.val) := by decide +kernel
lemma valid_part1_2 : FiniteIntervals.Covers ValidAt 10 11 :=
  FiniteIntervals.of_fin 10 1 valid_sub1_2
lemma valid_sub1_3 : ∀ i : Fin 1, ValidAt (11 + i.val) := by decide +kernel
lemma valid_part1_3 : FiniteIntervals.Covers ValidAt 11 12 :=
  FiniteIntervals.of_fin 11 1 valid_sub1_3
lemma valid_sub1_4 : ∀ i : Fin 1, ValidAt (12 + i.val) := by decide +kernel
lemma valid_part1_4 : FiniteIntervals.Covers ValidAt 12 13 :=
  FiniteIntervals.of_fin 12 1 valid_sub1_4
lemma valid_sub1_5 : ∀ i : Fin 1, ValidAt (13 + i.val) := by decide +kernel
lemma valid_part1_5 : FiniteIntervals.Covers ValidAt 13 14 :=
  FiniteIntervals.of_fin 13 1 valid_sub1_5
lemma valid_sub1_6 : ∀ i : Fin 1, ValidAt (14 + i.val) := by decide +kernel
lemma valid_part1_6 : FiniteIntervals.Covers ValidAt 14 15 :=
  FiniteIntervals.of_fin 14 1 valid_sub1_6
lemma valid_sub1_7 : ∀ i : Fin 1, ValidAt (15 + i.val) := by decide +kernel
lemma valid_part1_7 : FiniteIntervals.Covers ValidAt 15 16 :=
  FiniteIntervals.of_fin 15 1 valid_sub1_7
lemma valid_interval1 : FiniteIntervals.Covers ValidAt 8 16 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part1_0 valid_part1_1) (FiniteIntervals.merge valid_part1_2 valid_part1_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part1_4 valid_part1_5) (FiniteIntervals.merge valid_part1_6 valid_part1_7)))
#print axioms valid_interval1
end Erdos184Work.PureSixActions1
