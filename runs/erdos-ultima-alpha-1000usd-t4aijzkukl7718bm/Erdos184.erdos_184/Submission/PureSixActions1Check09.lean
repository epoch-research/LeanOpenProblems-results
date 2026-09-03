import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub9_0 : ∀ i : Fin 1, ValidAt (72 + i.val) := by decide +kernel
lemma valid_part9_0 : FiniteIntervals.Covers ValidAt 72 73 :=
  FiniteIntervals.of_fin 72 1 valid_sub9_0
lemma valid_sub9_1 : ∀ i : Fin 1, ValidAt (73 + i.val) := by decide +kernel
lemma valid_part9_1 : FiniteIntervals.Covers ValidAt 73 74 :=
  FiniteIntervals.of_fin 73 1 valid_sub9_1
lemma valid_sub9_2 : ∀ i : Fin 1, ValidAt (74 + i.val) := by decide +kernel
lemma valid_part9_2 : FiniteIntervals.Covers ValidAt 74 75 :=
  FiniteIntervals.of_fin 74 1 valid_sub9_2
lemma valid_sub9_3 : ∀ i : Fin 1, ValidAt (75 + i.val) := by decide +kernel
lemma valid_part9_3 : FiniteIntervals.Covers ValidAt 75 76 :=
  FiniteIntervals.of_fin 75 1 valid_sub9_3
lemma valid_sub9_4 : ∀ i : Fin 1, ValidAt (76 + i.val) := by decide +kernel
lemma valid_part9_4 : FiniteIntervals.Covers ValidAt 76 77 :=
  FiniteIntervals.of_fin 76 1 valid_sub9_4
lemma valid_sub9_5 : ∀ i : Fin 1, ValidAt (77 + i.val) := by decide +kernel
lemma valid_part9_5 : FiniteIntervals.Covers ValidAt 77 78 :=
  FiniteIntervals.of_fin 77 1 valid_sub9_5
lemma valid_sub9_6 : ∀ i : Fin 1, ValidAt (78 + i.val) := by decide +kernel
lemma valid_part9_6 : FiniteIntervals.Covers ValidAt 78 79 :=
  FiniteIntervals.of_fin 78 1 valid_sub9_6
lemma valid_sub9_7 : ∀ i : Fin 1, ValidAt (79 + i.val) := by decide +kernel
lemma valid_part9_7 : FiniteIntervals.Covers ValidAt 79 80 :=
  FiniteIntervals.of_fin 79 1 valid_sub9_7
lemma valid_interval9 : FiniteIntervals.Covers ValidAt 72 80 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part9_0 valid_part9_1) (FiniteIntervals.merge valid_part9_2 valid_part9_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part9_4 valid_part9_5) (FiniteIntervals.merge valid_part9_6 valid_part9_7)))
#print axioms valid_interval9
end Erdos184Work.PureSixActions1
