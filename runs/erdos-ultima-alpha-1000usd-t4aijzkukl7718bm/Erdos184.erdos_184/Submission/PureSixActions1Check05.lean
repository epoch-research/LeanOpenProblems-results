import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub5_0 : ∀ i : Fin 1, ValidAt (40 + i.val) := by decide +kernel
lemma valid_part5_0 : FiniteIntervals.Covers ValidAt 40 41 :=
  FiniteIntervals.of_fin 40 1 valid_sub5_0
lemma valid_sub5_1 : ∀ i : Fin 1, ValidAt (41 + i.val) := by decide +kernel
lemma valid_part5_1 : FiniteIntervals.Covers ValidAt 41 42 :=
  FiniteIntervals.of_fin 41 1 valid_sub5_1
lemma valid_sub5_2 : ∀ i : Fin 1, ValidAt (42 + i.val) := by decide +kernel
lemma valid_part5_2 : FiniteIntervals.Covers ValidAt 42 43 :=
  FiniteIntervals.of_fin 42 1 valid_sub5_2
lemma valid_sub5_3 : ∀ i : Fin 1, ValidAt (43 + i.val) := by decide +kernel
lemma valid_part5_3 : FiniteIntervals.Covers ValidAt 43 44 :=
  FiniteIntervals.of_fin 43 1 valid_sub5_3
lemma valid_sub5_4 : ∀ i : Fin 1, ValidAt (44 + i.val) := by decide +kernel
lemma valid_part5_4 : FiniteIntervals.Covers ValidAt 44 45 :=
  FiniteIntervals.of_fin 44 1 valid_sub5_4
lemma valid_sub5_5 : ∀ i : Fin 1, ValidAt (45 + i.val) := by decide +kernel
lemma valid_part5_5 : FiniteIntervals.Covers ValidAt 45 46 :=
  FiniteIntervals.of_fin 45 1 valid_sub5_5
lemma valid_sub5_6 : ∀ i : Fin 1, ValidAt (46 + i.val) := by decide +kernel
lemma valid_part5_6 : FiniteIntervals.Covers ValidAt 46 47 :=
  FiniteIntervals.of_fin 46 1 valid_sub5_6
lemma valid_sub5_7 : ∀ i : Fin 1, ValidAt (47 + i.val) := by decide +kernel
lemma valid_part5_7 : FiniteIntervals.Covers ValidAt 47 48 :=
  FiniteIntervals.of_fin 47 1 valid_sub5_7
lemma valid_interval5 : FiniteIntervals.Covers ValidAt 40 48 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part5_0 valid_part5_1) (FiniteIntervals.merge valid_part5_2 valid_part5_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part5_4 valid_part5_5) (FiniteIntervals.merge valid_part5_6 valid_part5_7)))
#print axioms valid_interval5
end Erdos184Work.PureSixActions1
