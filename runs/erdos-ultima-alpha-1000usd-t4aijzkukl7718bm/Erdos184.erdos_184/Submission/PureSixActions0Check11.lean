import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub11_0 : ∀ i : Fin 1, ValidAt (132 + i.val) := by decide +kernel
lemma valid_part11_0 : FiniteIntervals.Covers ValidAt 132 133 :=
  FiniteIntervals.of_fin 132 1 valid_sub11_0
lemma valid_sub11_1 : ∀ i : Fin 1, ValidAt (133 + i.val) := by decide +kernel
lemma valid_part11_1 : FiniteIntervals.Covers ValidAt 133 134 :=
  FiniteIntervals.of_fin 133 1 valid_sub11_1
lemma valid_sub11_2 : ∀ i : Fin 1, ValidAt (134 + i.val) := by decide +kernel
lemma valid_part11_2 : FiniteIntervals.Covers ValidAt 134 135 :=
  FiniteIntervals.of_fin 134 1 valid_sub11_2
lemma valid_sub11_3 : ∀ i : Fin 1, ValidAt (135 + i.val) := by decide +kernel
lemma valid_part11_3 : FiniteIntervals.Covers ValidAt 135 136 :=
  FiniteIntervals.of_fin 135 1 valid_sub11_3
lemma valid_sub11_4 : ∀ i : Fin 1, ValidAt (136 + i.val) := by decide +kernel
lemma valid_part11_4 : FiniteIntervals.Covers ValidAt 136 137 :=
  FiniteIntervals.of_fin 136 1 valid_sub11_4
lemma valid_sub11_5 : ∀ i : Fin 1, ValidAt (137 + i.val) := by decide +kernel
lemma valid_part11_5 : FiniteIntervals.Covers ValidAt 137 138 :=
  FiniteIntervals.of_fin 137 1 valid_sub11_5
lemma valid_sub11_6 : ∀ i : Fin 1, ValidAt (138 + i.val) := by decide +kernel
lemma valid_part11_6 : FiniteIntervals.Covers ValidAt 138 139 :=
  FiniteIntervals.of_fin 138 1 valid_sub11_6
lemma valid_sub11_7 : ∀ i : Fin 1, ValidAt (139 + i.val) := by decide +kernel
lemma valid_part11_7 : FiniteIntervals.Covers ValidAt 139 140 :=
  FiniteIntervals.of_fin 139 1 valid_sub11_7
lemma valid_sub11_8 : ∀ i : Fin 1, ValidAt (140 + i.val) := by decide +kernel
lemma valid_part11_8 : FiniteIntervals.Covers ValidAt 140 141 :=
  FiniteIntervals.of_fin 140 1 valid_sub11_8
lemma valid_sub11_9 : ∀ i : Fin 1, ValidAt (141 + i.val) := by decide +kernel
lemma valid_part11_9 : FiniteIntervals.Covers ValidAt 141 142 :=
  FiniteIntervals.of_fin 141 1 valid_sub11_9
lemma valid_sub11_10 : ∀ i : Fin 1, ValidAt (142 + i.val) := by decide +kernel
lemma valid_part11_10 : FiniteIntervals.Covers ValidAt 142 143 :=
  FiniteIntervals.of_fin 142 1 valid_sub11_10
lemma valid_sub11_11 : ∀ i : Fin 1, ValidAt (143 + i.val) := by decide +kernel
lemma valid_part11_11 : FiniteIntervals.Covers ValidAt 143 144 :=
  FiniteIntervals.of_fin 143 1 valid_sub11_11
lemma valid_interval11 : FiniteIntervals.Covers ValidAt 132 144 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part11_0 (FiniteIntervals.merge valid_part11_1 valid_part11_2)) (FiniteIntervals.merge valid_part11_3 (FiniteIntervals.merge valid_part11_4 valid_part11_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part11_6 (FiniteIntervals.merge valid_part11_7 valid_part11_8)) (FiniteIntervals.merge valid_part11_9 (FiniteIntervals.merge valid_part11_10 valid_part11_11))))
#print axioms valid_interval11
end Erdos184Work.PureSixActions0
