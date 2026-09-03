import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub4_0 : ∀ i : Fin 1, ValidAt (48 + i.val) := by decide +kernel
lemma valid_part4_0 : FiniteIntervals.Covers ValidAt 48 49 :=
  FiniteIntervals.of_fin 48 1 valid_sub4_0
lemma valid_sub4_1 : ∀ i : Fin 1, ValidAt (49 + i.val) := by decide +kernel
lemma valid_part4_1 : FiniteIntervals.Covers ValidAt 49 50 :=
  FiniteIntervals.of_fin 49 1 valid_sub4_1
lemma valid_sub4_2 : ∀ i : Fin 1, ValidAt (50 + i.val) := by decide +kernel
lemma valid_part4_2 : FiniteIntervals.Covers ValidAt 50 51 :=
  FiniteIntervals.of_fin 50 1 valid_sub4_2
lemma valid_sub4_3 : ∀ i : Fin 1, ValidAt (51 + i.val) := by decide +kernel
lemma valid_part4_3 : FiniteIntervals.Covers ValidAt 51 52 :=
  FiniteIntervals.of_fin 51 1 valid_sub4_3
lemma valid_sub4_4 : ∀ i : Fin 1, ValidAt (52 + i.val) := by decide +kernel
lemma valid_part4_4 : FiniteIntervals.Covers ValidAt 52 53 :=
  FiniteIntervals.of_fin 52 1 valid_sub4_4
lemma valid_sub4_5 : ∀ i : Fin 1, ValidAt (53 + i.val) := by decide +kernel
lemma valid_part4_5 : FiniteIntervals.Covers ValidAt 53 54 :=
  FiniteIntervals.of_fin 53 1 valid_sub4_5
lemma valid_sub4_6 : ∀ i : Fin 1, ValidAt (54 + i.val) := by decide +kernel
lemma valid_part4_6 : FiniteIntervals.Covers ValidAt 54 55 :=
  FiniteIntervals.of_fin 54 1 valid_sub4_6
lemma valid_sub4_7 : ∀ i : Fin 1, ValidAt (55 + i.val) := by decide +kernel
lemma valid_part4_7 : FiniteIntervals.Covers ValidAt 55 56 :=
  FiniteIntervals.of_fin 55 1 valid_sub4_7
lemma valid_sub4_8 : ∀ i : Fin 1, ValidAt (56 + i.val) := by decide +kernel
lemma valid_part4_8 : FiniteIntervals.Covers ValidAt 56 57 :=
  FiniteIntervals.of_fin 56 1 valid_sub4_8
lemma valid_sub4_9 : ∀ i : Fin 1, ValidAt (57 + i.val) := by decide +kernel
lemma valid_part4_9 : FiniteIntervals.Covers ValidAt 57 58 :=
  FiniteIntervals.of_fin 57 1 valid_sub4_9
lemma valid_sub4_10 : ∀ i : Fin 1, ValidAt (58 + i.val) := by decide +kernel
lemma valid_part4_10 : FiniteIntervals.Covers ValidAt 58 59 :=
  FiniteIntervals.of_fin 58 1 valid_sub4_10
lemma valid_sub4_11 : ∀ i : Fin 1, ValidAt (59 + i.val) := by decide +kernel
lemma valid_part4_11 : FiniteIntervals.Covers ValidAt 59 60 :=
  FiniteIntervals.of_fin 59 1 valid_sub4_11
lemma valid_interval4 : FiniteIntervals.Covers ValidAt 48 60 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part4_0 (FiniteIntervals.merge valid_part4_1 valid_part4_2)) (FiniteIntervals.merge valid_part4_3 (FiniteIntervals.merge valid_part4_4 valid_part4_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part4_6 (FiniteIntervals.merge valid_part4_7 valid_part4_8)) (FiniteIntervals.merge valid_part4_9 (FiniteIntervals.merge valid_part4_10 valid_part4_11))))
#print axioms valid_interval4
end Erdos184Work.PureSixActions0
