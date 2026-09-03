import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub5_0 : ∀ i : Fin 1, ValidAt (60 + i.val) := by decide +kernel
lemma valid_part5_0 : FiniteIntervals.Covers ValidAt 60 61 :=
  FiniteIntervals.of_fin 60 1 valid_sub5_0
lemma valid_sub5_1 : ∀ i : Fin 1, ValidAt (61 + i.val) := by decide +kernel
lemma valid_part5_1 : FiniteIntervals.Covers ValidAt 61 62 :=
  FiniteIntervals.of_fin 61 1 valid_sub5_1
lemma valid_sub5_2 : ∀ i : Fin 1, ValidAt (62 + i.val) := by decide +kernel
lemma valid_part5_2 : FiniteIntervals.Covers ValidAt 62 63 :=
  FiniteIntervals.of_fin 62 1 valid_sub5_2
lemma valid_sub5_3 : ∀ i : Fin 1, ValidAt (63 + i.val) := by decide +kernel
lemma valid_part5_3 : FiniteIntervals.Covers ValidAt 63 64 :=
  FiniteIntervals.of_fin 63 1 valid_sub5_3
lemma valid_sub5_4 : ∀ i : Fin 1, ValidAt (64 + i.val) := by decide +kernel
lemma valid_part5_4 : FiniteIntervals.Covers ValidAt 64 65 :=
  FiniteIntervals.of_fin 64 1 valid_sub5_4
lemma valid_sub5_5 : ∀ i : Fin 1, ValidAt (65 + i.val) := by decide +kernel
lemma valid_part5_5 : FiniteIntervals.Covers ValidAt 65 66 :=
  FiniteIntervals.of_fin 65 1 valid_sub5_5
lemma valid_sub5_6 : ∀ i : Fin 1, ValidAt (66 + i.val) := by decide +kernel
lemma valid_part5_6 : FiniteIntervals.Covers ValidAt 66 67 :=
  FiniteIntervals.of_fin 66 1 valid_sub5_6
lemma valid_sub5_7 : ∀ i : Fin 1, ValidAt (67 + i.val) := by decide +kernel
lemma valid_part5_7 : FiniteIntervals.Covers ValidAt 67 68 :=
  FiniteIntervals.of_fin 67 1 valid_sub5_7
lemma valid_sub5_8 : ∀ i : Fin 1, ValidAt (68 + i.val) := by decide +kernel
lemma valid_part5_8 : FiniteIntervals.Covers ValidAt 68 69 :=
  FiniteIntervals.of_fin 68 1 valid_sub5_8
lemma valid_sub5_9 : ∀ i : Fin 1, ValidAt (69 + i.val) := by decide +kernel
lemma valid_part5_9 : FiniteIntervals.Covers ValidAt 69 70 :=
  FiniteIntervals.of_fin 69 1 valid_sub5_9
lemma valid_sub5_10 : ∀ i : Fin 1, ValidAt (70 + i.val) := by decide +kernel
lemma valid_part5_10 : FiniteIntervals.Covers ValidAt 70 71 :=
  FiniteIntervals.of_fin 70 1 valid_sub5_10
lemma valid_sub5_11 : ∀ i : Fin 1, ValidAt (71 + i.val) := by decide +kernel
lemma valid_part5_11 : FiniteIntervals.Covers ValidAt 71 72 :=
  FiniteIntervals.of_fin 71 1 valid_sub5_11
lemma valid_interval5 : FiniteIntervals.Covers ValidAt 60 72 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part5_0 (FiniteIntervals.merge valid_part5_1 valid_part5_2)) (FiniteIntervals.merge valid_part5_3 (FiniteIntervals.merge valid_part5_4 valid_part5_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part5_6 (FiniteIntervals.merge valid_part5_7 valid_part5_8)) (FiniteIntervals.merge valid_part5_9 (FiniteIntervals.merge valid_part5_10 valid_part5_11))))
#print axioms valid_interval5
end Erdos184Work.PureSixActions0
