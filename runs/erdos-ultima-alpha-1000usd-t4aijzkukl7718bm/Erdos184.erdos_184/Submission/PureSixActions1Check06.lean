import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub6_0 : ∀ i : Fin 1, ValidAt (48 + i.val) := by decide +kernel
lemma valid_part6_0 : FiniteIntervals.Covers ValidAt 48 49 :=
  FiniteIntervals.of_fin 48 1 valid_sub6_0
lemma valid_sub6_1 : ∀ i : Fin 1, ValidAt (49 + i.val) := by decide +kernel
lemma valid_part6_1 : FiniteIntervals.Covers ValidAt 49 50 :=
  FiniteIntervals.of_fin 49 1 valid_sub6_1
lemma valid_sub6_2 : ∀ i : Fin 1, ValidAt (50 + i.val) := by decide +kernel
lemma valid_part6_2 : FiniteIntervals.Covers ValidAt 50 51 :=
  FiniteIntervals.of_fin 50 1 valid_sub6_2
lemma valid_sub6_3 : ∀ i : Fin 1, ValidAt (51 + i.val) := by decide +kernel
lemma valid_part6_3 : FiniteIntervals.Covers ValidAt 51 52 :=
  FiniteIntervals.of_fin 51 1 valid_sub6_3
lemma valid_sub6_4 : ∀ i : Fin 1, ValidAt (52 + i.val) := by decide +kernel
lemma valid_part6_4 : FiniteIntervals.Covers ValidAt 52 53 :=
  FiniteIntervals.of_fin 52 1 valid_sub6_4
lemma valid_sub6_5 : ∀ i : Fin 1, ValidAt (53 + i.val) := by decide +kernel
lemma valid_part6_5 : FiniteIntervals.Covers ValidAt 53 54 :=
  FiniteIntervals.of_fin 53 1 valid_sub6_5
lemma valid_sub6_6 : ∀ i : Fin 1, ValidAt (54 + i.val) := by decide +kernel
lemma valid_part6_6 : FiniteIntervals.Covers ValidAt 54 55 :=
  FiniteIntervals.of_fin 54 1 valid_sub6_6
lemma valid_sub6_7 : ∀ i : Fin 1, ValidAt (55 + i.val) := by decide +kernel
lemma valid_part6_7 : FiniteIntervals.Covers ValidAt 55 56 :=
  FiniteIntervals.of_fin 55 1 valid_sub6_7
lemma valid_interval6 : FiniteIntervals.Covers ValidAt 48 56 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part6_0 valid_part6_1) (FiniteIntervals.merge valid_part6_2 valid_part6_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part6_4 valid_part6_5) (FiniteIntervals.merge valid_part6_6 valid_part6_7)))
#print axioms valid_interval6
end Erdos184Work.PureSixActions1
