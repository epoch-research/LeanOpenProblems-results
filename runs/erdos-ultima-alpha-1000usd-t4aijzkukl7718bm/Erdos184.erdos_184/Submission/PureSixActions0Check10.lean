import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub10_0 : ∀ i : Fin 1, ValidAt (120 + i.val) := by decide +kernel
lemma valid_part10_0 : FiniteIntervals.Covers ValidAt 120 121 :=
  FiniteIntervals.of_fin 120 1 valid_sub10_0
lemma valid_sub10_1 : ∀ i : Fin 1, ValidAt (121 + i.val) := by decide +kernel
lemma valid_part10_1 : FiniteIntervals.Covers ValidAt 121 122 :=
  FiniteIntervals.of_fin 121 1 valid_sub10_1
lemma valid_sub10_2 : ∀ i : Fin 1, ValidAt (122 + i.val) := by decide +kernel
lemma valid_part10_2 : FiniteIntervals.Covers ValidAt 122 123 :=
  FiniteIntervals.of_fin 122 1 valid_sub10_2
lemma valid_sub10_3 : ∀ i : Fin 1, ValidAt (123 + i.val) := by decide +kernel
lemma valid_part10_3 : FiniteIntervals.Covers ValidAt 123 124 :=
  FiniteIntervals.of_fin 123 1 valid_sub10_3
lemma valid_sub10_4 : ∀ i : Fin 1, ValidAt (124 + i.val) := by decide +kernel
lemma valid_part10_4 : FiniteIntervals.Covers ValidAt 124 125 :=
  FiniteIntervals.of_fin 124 1 valid_sub10_4
lemma valid_sub10_5 : ∀ i : Fin 1, ValidAt (125 + i.val) := by decide +kernel
lemma valid_part10_5 : FiniteIntervals.Covers ValidAt 125 126 :=
  FiniteIntervals.of_fin 125 1 valid_sub10_5
lemma valid_sub10_6 : ∀ i : Fin 1, ValidAt (126 + i.val) := by decide +kernel
lemma valid_part10_6 : FiniteIntervals.Covers ValidAt 126 127 :=
  FiniteIntervals.of_fin 126 1 valid_sub10_6
lemma valid_sub10_7 : ∀ i : Fin 1, ValidAt (127 + i.val) := by decide +kernel
lemma valid_part10_7 : FiniteIntervals.Covers ValidAt 127 128 :=
  FiniteIntervals.of_fin 127 1 valid_sub10_7
lemma valid_sub10_8 : ∀ i : Fin 1, ValidAt (128 + i.val) := by decide +kernel
lemma valid_part10_8 : FiniteIntervals.Covers ValidAt 128 129 :=
  FiniteIntervals.of_fin 128 1 valid_sub10_8
lemma valid_sub10_9 : ∀ i : Fin 1, ValidAt (129 + i.val) := by decide +kernel
lemma valid_part10_9 : FiniteIntervals.Covers ValidAt 129 130 :=
  FiniteIntervals.of_fin 129 1 valid_sub10_9
lemma valid_sub10_10 : ∀ i : Fin 1, ValidAt (130 + i.val) := by decide +kernel
lemma valid_part10_10 : FiniteIntervals.Covers ValidAt 130 131 :=
  FiniteIntervals.of_fin 130 1 valid_sub10_10
lemma valid_sub10_11 : ∀ i : Fin 1, ValidAt (131 + i.val) := by decide +kernel
lemma valid_part10_11 : FiniteIntervals.Covers ValidAt 131 132 :=
  FiniteIntervals.of_fin 131 1 valid_sub10_11
lemma valid_interval10 : FiniteIntervals.Covers ValidAt 120 132 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part10_0 (FiniteIntervals.merge valid_part10_1 valid_part10_2)) (FiniteIntervals.merge valid_part10_3 (FiniteIntervals.merge valid_part10_4 valid_part10_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part10_6 (FiniteIntervals.merge valid_part10_7 valid_part10_8)) (FiniteIntervals.merge valid_part10_9 (FiniteIntervals.merge valid_part10_10 valid_part10_11))))
#print axioms valid_interval10
end Erdos184Work.PureSixActions0
