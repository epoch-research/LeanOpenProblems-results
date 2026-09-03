import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub2_0 : ∀ i : Fin 1, ValidAt (24 + i.val) := by decide +kernel
lemma valid_part2_0 : FiniteIntervals.Covers ValidAt 24 25 :=
  FiniteIntervals.of_fin 24 1 valid_sub2_0
lemma valid_sub2_1 : ∀ i : Fin 1, ValidAt (25 + i.val) := by decide +kernel
lemma valid_part2_1 : FiniteIntervals.Covers ValidAt 25 26 :=
  FiniteIntervals.of_fin 25 1 valid_sub2_1
lemma valid_sub2_2 : ∀ i : Fin 1, ValidAt (26 + i.val) := by decide +kernel
lemma valid_part2_2 : FiniteIntervals.Covers ValidAt 26 27 :=
  FiniteIntervals.of_fin 26 1 valid_sub2_2
lemma valid_sub2_3 : ∀ i : Fin 1, ValidAt (27 + i.val) := by decide +kernel
lemma valid_part2_3 : FiniteIntervals.Covers ValidAt 27 28 :=
  FiniteIntervals.of_fin 27 1 valid_sub2_3
lemma valid_sub2_4 : ∀ i : Fin 1, ValidAt (28 + i.val) := by decide +kernel
lemma valid_part2_4 : FiniteIntervals.Covers ValidAt 28 29 :=
  FiniteIntervals.of_fin 28 1 valid_sub2_4
lemma valid_sub2_5 : ∀ i : Fin 1, ValidAt (29 + i.val) := by decide +kernel
lemma valid_part2_5 : FiniteIntervals.Covers ValidAt 29 30 :=
  FiniteIntervals.of_fin 29 1 valid_sub2_5
lemma valid_sub2_6 : ∀ i : Fin 1, ValidAt (30 + i.val) := by decide +kernel
lemma valid_part2_6 : FiniteIntervals.Covers ValidAt 30 31 :=
  FiniteIntervals.of_fin 30 1 valid_sub2_6
lemma valid_sub2_7 : ∀ i : Fin 1, ValidAt (31 + i.val) := by decide +kernel
lemma valid_part2_7 : FiniteIntervals.Covers ValidAt 31 32 :=
  FiniteIntervals.of_fin 31 1 valid_sub2_7
lemma valid_sub2_8 : ∀ i : Fin 1, ValidAt (32 + i.val) := by decide +kernel
lemma valid_part2_8 : FiniteIntervals.Covers ValidAt 32 33 :=
  FiniteIntervals.of_fin 32 1 valid_sub2_8
lemma valid_sub2_9 : ∀ i : Fin 1, ValidAt (33 + i.val) := by decide +kernel
lemma valid_part2_9 : FiniteIntervals.Covers ValidAt 33 34 :=
  FiniteIntervals.of_fin 33 1 valid_sub2_9
lemma valid_sub2_10 : ∀ i : Fin 1, ValidAt (34 + i.val) := by decide +kernel
lemma valid_part2_10 : FiniteIntervals.Covers ValidAt 34 35 :=
  FiniteIntervals.of_fin 34 1 valid_sub2_10
lemma valid_sub2_11 : ∀ i : Fin 1, ValidAt (35 + i.val) := by decide +kernel
lemma valid_part2_11 : FiniteIntervals.Covers ValidAt 35 36 :=
  FiniteIntervals.of_fin 35 1 valid_sub2_11
lemma valid_interval2 : FiniteIntervals.Covers ValidAt 24 36 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part2_0 (FiniteIntervals.merge valid_part2_1 valid_part2_2)) (FiniteIntervals.merge valid_part2_3 (FiniteIntervals.merge valid_part2_4 valid_part2_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part2_6 (FiniteIntervals.merge valid_part2_7 valid_part2_8)) (FiniteIntervals.merge valid_part2_9 (FiniteIntervals.merge valid_part2_10 valid_part2_11))))
#print axioms valid_interval2
end Erdos184Work.PureSixActions0
