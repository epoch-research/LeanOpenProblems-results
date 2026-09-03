import Submission.PureSixActions1Base
namespace Erdos184Work.PureSixActions1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub11_0 : ∀ i : Fin 1, ValidAt (88 + i.val) := by decide +kernel
lemma valid_part11_0 : FiniteIntervals.Covers ValidAt 88 89 :=
  FiniteIntervals.of_fin 88 1 valid_sub11_0
lemma valid_sub11_1 : ∀ i : Fin 1, ValidAt (89 + i.val) := by decide +kernel
lemma valid_part11_1 : FiniteIntervals.Covers ValidAt 89 90 :=
  FiniteIntervals.of_fin 89 1 valid_sub11_1
lemma valid_sub11_2 : ∀ i : Fin 1, ValidAt (90 + i.val) := by decide +kernel
lemma valid_part11_2 : FiniteIntervals.Covers ValidAt 90 91 :=
  FiniteIntervals.of_fin 90 1 valid_sub11_2
lemma valid_sub11_3 : ∀ i : Fin 1, ValidAt (91 + i.val) := by decide +kernel
lemma valid_part11_3 : FiniteIntervals.Covers ValidAt 91 92 :=
  FiniteIntervals.of_fin 91 1 valid_sub11_3
lemma valid_sub11_4 : ∀ i : Fin 1, ValidAt (92 + i.val) := by decide +kernel
lemma valid_part11_4 : FiniteIntervals.Covers ValidAt 92 93 :=
  FiniteIntervals.of_fin 92 1 valid_sub11_4
lemma valid_sub11_5 : ∀ i : Fin 1, ValidAt (93 + i.val) := by decide +kernel
lemma valid_part11_5 : FiniteIntervals.Covers ValidAt 93 94 :=
  FiniteIntervals.of_fin 93 1 valid_sub11_5
lemma valid_sub11_6 : ∀ i : Fin 1, ValidAt (94 + i.val) := by decide +kernel
lemma valid_part11_6 : FiniteIntervals.Covers ValidAt 94 95 :=
  FiniteIntervals.of_fin 94 1 valid_sub11_6
lemma valid_sub11_7 : ∀ i : Fin 1, ValidAt (95 + i.val) := by decide +kernel
lemma valid_part11_7 : FiniteIntervals.Covers ValidAt 95 96 :=
  FiniteIntervals.of_fin 95 1 valid_sub11_7
lemma valid_interval11 : FiniteIntervals.Covers ValidAt 88 96 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part11_0 valid_part11_1) (FiniteIntervals.merge valid_part11_2 valid_part11_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part11_4 valid_part11_5) (FiniteIntervals.merge valid_part11_6 valid_part11_7)))
#print axioms valid_interval11
end Erdos184Work.PureSixActions1
