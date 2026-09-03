import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub4_0 : ∀ i : Fin 1, ValidAt (32 + i.val) := by decide +kernel
lemma valid_part4_0 : FiniteIntervals.Covers ValidAt 32 33 :=
  FiniteIntervals.of_fin 32 1 valid_sub4_0
lemma valid_sub4_1 : ∀ i : Fin 1, ValidAt (33 + i.val) := by decide +kernel
lemma valid_part4_1 : FiniteIntervals.Covers ValidAt 33 34 :=
  FiniteIntervals.of_fin 33 1 valid_sub4_1
lemma valid_sub4_2 : ∀ i : Fin 1, ValidAt (34 + i.val) := by decide +kernel
lemma valid_part4_2 : FiniteIntervals.Covers ValidAt 34 35 :=
  FiniteIntervals.of_fin 34 1 valid_sub4_2
lemma valid_sub4_3 : ∀ i : Fin 1, ValidAt (35 + i.val) := by decide +kernel
lemma valid_part4_3 : FiniteIntervals.Covers ValidAt 35 36 :=
  FiniteIntervals.of_fin 35 1 valid_sub4_3
lemma valid_sub4_4 : ∀ i : Fin 1, ValidAt (36 + i.val) := by decide +kernel
lemma valid_part4_4 : FiniteIntervals.Covers ValidAt 36 37 :=
  FiniteIntervals.of_fin 36 1 valid_sub4_4
lemma valid_sub4_5 : ∀ i : Fin 1, ValidAt (37 + i.val) := by decide +kernel
lemma valid_part4_5 : FiniteIntervals.Covers ValidAt 37 38 :=
  FiniteIntervals.of_fin 37 1 valid_sub4_5
lemma valid_sub4_6 : ∀ i : Fin 1, ValidAt (38 + i.val) := by decide +kernel
lemma valid_part4_6 : FiniteIntervals.Covers ValidAt 38 39 :=
  FiniteIntervals.of_fin 38 1 valid_sub4_6
lemma valid_sub4_7 : ∀ i : Fin 1, ValidAt (39 + i.val) := by decide +kernel
lemma valid_part4_7 : FiniteIntervals.Covers ValidAt 39 40 :=
  FiniteIntervals.of_fin 39 1 valid_sub4_7
lemma valid_interval4 : FiniteIntervals.Covers ValidAt 32 40 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part4_0 valid_part4_1) (FiniteIntervals.merge valid_part4_2 valid_part4_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part4_4 valid_part4_5) (FiniteIntervals.merge valid_part4_6 valid_part4_7)))
#print axioms valid_interval4
end Erdos184Work.PureSixActions1
