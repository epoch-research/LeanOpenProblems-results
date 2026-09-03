import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub6_0 : ∀ i : Fin 1, ValidAt (72 + i.val) := by decide +kernel
lemma valid_part6_0 : FiniteIntervals.Covers ValidAt 72 73 :=
  FiniteIntervals.of_fin 72 1 valid_sub6_0
lemma valid_sub6_1 : ∀ i : Fin 1, ValidAt (73 + i.val) := by decide +kernel
lemma valid_part6_1 : FiniteIntervals.Covers ValidAt 73 74 :=
  FiniteIntervals.of_fin 73 1 valid_sub6_1
lemma valid_sub6_2 : ∀ i : Fin 1, ValidAt (74 + i.val) := by decide +kernel
lemma valid_part6_2 : FiniteIntervals.Covers ValidAt 74 75 :=
  FiniteIntervals.of_fin 74 1 valid_sub6_2
lemma valid_sub6_3 : ∀ i : Fin 1, ValidAt (75 + i.val) := by decide +kernel
lemma valid_part6_3 : FiniteIntervals.Covers ValidAt 75 76 :=
  FiniteIntervals.of_fin 75 1 valid_sub6_3
lemma valid_sub6_4 : ∀ i : Fin 1, ValidAt (76 + i.val) := by decide +kernel
lemma valid_part6_4 : FiniteIntervals.Covers ValidAt 76 77 :=
  FiniteIntervals.of_fin 76 1 valid_sub6_4
lemma valid_sub6_5 : ∀ i : Fin 1, ValidAt (77 + i.val) := by decide +kernel
lemma valid_part6_5 : FiniteIntervals.Covers ValidAt 77 78 :=
  FiniteIntervals.of_fin 77 1 valid_sub6_5
lemma valid_sub6_6 : ∀ i : Fin 1, ValidAt (78 + i.val) := by decide +kernel
lemma valid_part6_6 : FiniteIntervals.Covers ValidAt 78 79 :=
  FiniteIntervals.of_fin 78 1 valid_sub6_6
lemma valid_sub6_7 : ∀ i : Fin 1, ValidAt (79 + i.val) := by decide +kernel
lemma valid_part6_7 : FiniteIntervals.Covers ValidAt 79 80 :=
  FiniteIntervals.of_fin 79 1 valid_sub6_7
lemma valid_sub6_8 : ∀ i : Fin 1, ValidAt (80 + i.val) := by decide +kernel
lemma valid_part6_8 : FiniteIntervals.Covers ValidAt 80 81 :=
  FiniteIntervals.of_fin 80 1 valid_sub6_8
lemma valid_sub6_9 : ∀ i : Fin 1, ValidAt (81 + i.val) := by decide +kernel
lemma valid_part6_9 : FiniteIntervals.Covers ValidAt 81 82 :=
  FiniteIntervals.of_fin 81 1 valid_sub6_9
lemma valid_sub6_10 : ∀ i : Fin 1, ValidAt (82 + i.val) := by decide +kernel
lemma valid_part6_10 : FiniteIntervals.Covers ValidAt 82 83 :=
  FiniteIntervals.of_fin 82 1 valid_sub6_10
lemma valid_sub6_11 : ∀ i : Fin 1, ValidAt (83 + i.val) := by decide +kernel
lemma valid_part6_11 : FiniteIntervals.Covers ValidAt 83 84 :=
  FiniteIntervals.of_fin 83 1 valid_sub6_11
lemma valid_interval6 : FiniteIntervals.Covers ValidAt 72 84 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part6_0 (FiniteIntervals.merge valid_part6_1 valid_part6_2)) (FiniteIntervals.merge valid_part6_3 (FiniteIntervals.merge valid_part6_4 valid_part6_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part6_6 (FiniteIntervals.merge valid_part6_7 valid_part6_8)) (FiniteIntervals.merge valid_part6_9 (FiniteIntervals.merge valid_part6_10 valid_part6_11))))
#print axioms valid_interval6
end Erdos184Work.PureSixActions0
