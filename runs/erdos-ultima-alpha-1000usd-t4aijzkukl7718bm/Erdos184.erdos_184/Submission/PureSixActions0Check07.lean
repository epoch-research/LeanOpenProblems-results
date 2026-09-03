import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub7_0 : ∀ i : Fin 1, ValidAt (84 + i.val) := by decide +kernel
lemma valid_part7_0 : FiniteIntervals.Covers ValidAt 84 85 :=
  FiniteIntervals.of_fin 84 1 valid_sub7_0
lemma valid_sub7_1 : ∀ i : Fin 1, ValidAt (85 + i.val) := by decide +kernel
lemma valid_part7_1 : FiniteIntervals.Covers ValidAt 85 86 :=
  FiniteIntervals.of_fin 85 1 valid_sub7_1
lemma valid_sub7_2 : ∀ i : Fin 1, ValidAt (86 + i.val) := by decide +kernel
lemma valid_part7_2 : FiniteIntervals.Covers ValidAt 86 87 :=
  FiniteIntervals.of_fin 86 1 valid_sub7_2
lemma valid_sub7_3 : ∀ i : Fin 1, ValidAt (87 + i.val) := by decide +kernel
lemma valid_part7_3 : FiniteIntervals.Covers ValidAt 87 88 :=
  FiniteIntervals.of_fin 87 1 valid_sub7_3
lemma valid_sub7_4 : ∀ i : Fin 1, ValidAt (88 + i.val) := by decide +kernel
lemma valid_part7_4 : FiniteIntervals.Covers ValidAt 88 89 :=
  FiniteIntervals.of_fin 88 1 valid_sub7_4
lemma valid_sub7_5 : ∀ i : Fin 1, ValidAt (89 + i.val) := by decide +kernel
lemma valid_part7_5 : FiniteIntervals.Covers ValidAt 89 90 :=
  FiniteIntervals.of_fin 89 1 valid_sub7_5
lemma valid_sub7_6 : ∀ i : Fin 1, ValidAt (90 + i.val) := by decide +kernel
lemma valid_part7_6 : FiniteIntervals.Covers ValidAt 90 91 :=
  FiniteIntervals.of_fin 90 1 valid_sub7_6
lemma valid_sub7_7 : ∀ i : Fin 1, ValidAt (91 + i.val) := by decide +kernel
lemma valid_part7_7 : FiniteIntervals.Covers ValidAt 91 92 :=
  FiniteIntervals.of_fin 91 1 valid_sub7_7
lemma valid_sub7_8 : ∀ i : Fin 1, ValidAt (92 + i.val) := by decide +kernel
lemma valid_part7_8 : FiniteIntervals.Covers ValidAt 92 93 :=
  FiniteIntervals.of_fin 92 1 valid_sub7_8
lemma valid_sub7_9 : ∀ i : Fin 1, ValidAt (93 + i.val) := by decide +kernel
lemma valid_part7_9 : FiniteIntervals.Covers ValidAt 93 94 :=
  FiniteIntervals.of_fin 93 1 valid_sub7_9
lemma valid_sub7_10 : ∀ i : Fin 1, ValidAt (94 + i.val) := by decide +kernel
lemma valid_part7_10 : FiniteIntervals.Covers ValidAt 94 95 :=
  FiniteIntervals.of_fin 94 1 valid_sub7_10
lemma valid_sub7_11 : ∀ i : Fin 1, ValidAt (95 + i.val) := by decide +kernel
lemma valid_part7_11 : FiniteIntervals.Covers ValidAt 95 96 :=
  FiniteIntervals.of_fin 95 1 valid_sub7_11
lemma valid_interval7 : FiniteIntervals.Covers ValidAt 84 96 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part7_0 (FiniteIntervals.merge valid_part7_1 valid_part7_2)) (FiniteIntervals.merge valid_part7_3 (FiniteIntervals.merge valid_part7_4 valid_part7_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part7_6 (FiniteIntervals.merge valid_part7_7 valid_part7_8)) (FiniteIntervals.merge valid_part7_9 (FiniteIntervals.merge valid_part7_10 valid_part7_11))))
#print axioms valid_interval7
end Erdos184Work.PureSixActions0
