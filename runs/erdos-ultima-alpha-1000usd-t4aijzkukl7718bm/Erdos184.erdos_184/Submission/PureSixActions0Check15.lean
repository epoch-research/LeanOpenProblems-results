import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub15_0 : ∀ i : Fin 1, ValidAt (180 + i.val) := by decide +kernel
lemma valid_part15_0 : FiniteIntervals.Covers ValidAt 180 181 :=
  FiniteIntervals.of_fin 180 1 valid_sub15_0
lemma valid_sub15_1 : ∀ i : Fin 1, ValidAt (181 + i.val) := by decide +kernel
lemma valid_part15_1 : FiniteIntervals.Covers ValidAt 181 182 :=
  FiniteIntervals.of_fin 181 1 valid_sub15_1
lemma valid_sub15_2 : ∀ i : Fin 1, ValidAt (182 + i.val) := by decide +kernel
lemma valid_part15_2 : FiniteIntervals.Covers ValidAt 182 183 :=
  FiniteIntervals.of_fin 182 1 valid_sub15_2
lemma valid_sub15_3 : ∀ i : Fin 1, ValidAt (183 + i.val) := by decide +kernel
lemma valid_part15_3 : FiniteIntervals.Covers ValidAt 183 184 :=
  FiniteIntervals.of_fin 183 1 valid_sub15_3
lemma valid_sub15_4 : ∀ i : Fin 1, ValidAt (184 + i.val) := by decide +kernel
lemma valid_part15_4 : FiniteIntervals.Covers ValidAt 184 185 :=
  FiniteIntervals.of_fin 184 1 valid_sub15_4
lemma valid_sub15_5 : ∀ i : Fin 1, ValidAt (185 + i.val) := by decide +kernel
lemma valid_part15_5 : FiniteIntervals.Covers ValidAt 185 186 :=
  FiniteIntervals.of_fin 185 1 valid_sub15_5
lemma valid_sub15_6 : ∀ i : Fin 1, ValidAt (186 + i.val) := by decide +kernel
lemma valid_part15_6 : FiniteIntervals.Covers ValidAt 186 187 :=
  FiniteIntervals.of_fin 186 1 valid_sub15_6
lemma valid_sub15_7 : ∀ i : Fin 1, ValidAt (187 + i.val) := by decide +kernel
lemma valid_part15_7 : FiniteIntervals.Covers ValidAt 187 188 :=
  FiniteIntervals.of_fin 187 1 valid_sub15_7
lemma valid_sub15_8 : ∀ i : Fin 1, ValidAt (188 + i.val) := by decide +kernel
lemma valid_part15_8 : FiniteIntervals.Covers ValidAt 188 189 :=
  FiniteIntervals.of_fin 188 1 valid_sub15_8
lemma valid_sub15_9 : ∀ i : Fin 1, ValidAt (189 + i.val) := by decide +kernel
lemma valid_part15_9 : FiniteIntervals.Covers ValidAt 189 190 :=
  FiniteIntervals.of_fin 189 1 valid_sub15_9
lemma valid_sub15_10 : ∀ i : Fin 1, ValidAt (190 + i.val) := by decide +kernel
lemma valid_part15_10 : FiniteIntervals.Covers ValidAt 190 191 :=
  FiniteIntervals.of_fin 190 1 valid_sub15_10
lemma valid_sub15_11 : ∀ i : Fin 1, ValidAt (191 + i.val) := by decide +kernel
lemma valid_part15_11 : FiniteIntervals.Covers ValidAt 191 192 :=
  FiniteIntervals.of_fin 191 1 valid_sub15_11
lemma valid_interval15 : FiniteIntervals.Covers ValidAt 180 192 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part15_0 (FiniteIntervals.merge valid_part15_1 valid_part15_2)) (FiniteIntervals.merge valid_part15_3 (FiniteIntervals.merge valid_part15_4 valid_part15_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part15_6 (FiniteIntervals.merge valid_part15_7 valid_part15_8)) (FiniteIntervals.merge valid_part15_9 (FiniteIntervals.merge valid_part15_10 valid_part15_11))))
#print axioms valid_interval15
end Erdos184Work.PureSixActions0
