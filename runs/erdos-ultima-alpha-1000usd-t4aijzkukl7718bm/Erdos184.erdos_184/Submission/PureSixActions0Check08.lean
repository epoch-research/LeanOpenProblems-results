import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub8_0 : ∀ i : Fin 1, ValidAt (96 + i.val) := by decide +kernel
lemma valid_part8_0 : FiniteIntervals.Covers ValidAt 96 97 :=
  FiniteIntervals.of_fin 96 1 valid_sub8_0
lemma valid_sub8_1 : ∀ i : Fin 1, ValidAt (97 + i.val) := by decide +kernel
lemma valid_part8_1 : FiniteIntervals.Covers ValidAt 97 98 :=
  FiniteIntervals.of_fin 97 1 valid_sub8_1
lemma valid_sub8_2 : ∀ i : Fin 1, ValidAt (98 + i.val) := by decide +kernel
lemma valid_part8_2 : FiniteIntervals.Covers ValidAt 98 99 :=
  FiniteIntervals.of_fin 98 1 valid_sub8_2
lemma valid_sub8_3 : ∀ i : Fin 1, ValidAt (99 + i.val) := by decide +kernel
lemma valid_part8_3 : FiniteIntervals.Covers ValidAt 99 100 :=
  FiniteIntervals.of_fin 99 1 valid_sub8_3
lemma valid_sub8_4 : ∀ i : Fin 1, ValidAt (100 + i.val) := by decide +kernel
lemma valid_part8_4 : FiniteIntervals.Covers ValidAt 100 101 :=
  FiniteIntervals.of_fin 100 1 valid_sub8_4
lemma valid_sub8_5 : ∀ i : Fin 1, ValidAt (101 + i.val) := by decide +kernel
lemma valid_part8_5 : FiniteIntervals.Covers ValidAt 101 102 :=
  FiniteIntervals.of_fin 101 1 valid_sub8_5
lemma valid_sub8_6 : ∀ i : Fin 1, ValidAt (102 + i.val) := by decide +kernel
lemma valid_part8_6 : FiniteIntervals.Covers ValidAt 102 103 :=
  FiniteIntervals.of_fin 102 1 valid_sub8_6
lemma valid_sub8_7 : ∀ i : Fin 1, ValidAt (103 + i.val) := by decide +kernel
lemma valid_part8_7 : FiniteIntervals.Covers ValidAt 103 104 :=
  FiniteIntervals.of_fin 103 1 valid_sub8_7
lemma valid_sub8_8 : ∀ i : Fin 1, ValidAt (104 + i.val) := by decide +kernel
lemma valid_part8_8 : FiniteIntervals.Covers ValidAt 104 105 :=
  FiniteIntervals.of_fin 104 1 valid_sub8_8
lemma valid_sub8_9 : ∀ i : Fin 1, ValidAt (105 + i.val) := by decide +kernel
lemma valid_part8_9 : FiniteIntervals.Covers ValidAt 105 106 :=
  FiniteIntervals.of_fin 105 1 valid_sub8_9
lemma valid_sub8_10 : ∀ i : Fin 1, ValidAt (106 + i.val) := by decide +kernel
lemma valid_part8_10 : FiniteIntervals.Covers ValidAt 106 107 :=
  FiniteIntervals.of_fin 106 1 valid_sub8_10
lemma valid_sub8_11 : ∀ i : Fin 1, ValidAt (107 + i.val) := by decide +kernel
lemma valid_part8_11 : FiniteIntervals.Covers ValidAt 107 108 :=
  FiniteIntervals.of_fin 107 1 valid_sub8_11
lemma valid_interval8 : FiniteIntervals.Covers ValidAt 96 108 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part8_0 (FiniteIntervals.merge valid_part8_1 valid_part8_2)) (FiniteIntervals.merge valid_part8_3 (FiniteIntervals.merge valid_part8_4 valid_part8_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part8_6 (FiniteIntervals.merge valid_part8_7 valid_part8_8)) (FiniteIntervals.merge valid_part8_9 (FiniteIntervals.merge valid_part8_10 valid_part8_11))))
#print axioms valid_interval8
end Erdos184Work.PureSixActions0
