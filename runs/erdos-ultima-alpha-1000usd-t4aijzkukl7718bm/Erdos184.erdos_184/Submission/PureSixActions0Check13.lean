import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub13_0 : ∀ i : Fin 1, ValidAt (156 + i.val) := by decide +kernel
lemma valid_part13_0 : FiniteIntervals.Covers ValidAt 156 157 :=
  FiniteIntervals.of_fin 156 1 valid_sub13_0
lemma valid_sub13_1 : ∀ i : Fin 1, ValidAt (157 + i.val) := by decide +kernel
lemma valid_part13_1 : FiniteIntervals.Covers ValidAt 157 158 :=
  FiniteIntervals.of_fin 157 1 valid_sub13_1
lemma valid_sub13_2 : ∀ i : Fin 1, ValidAt (158 + i.val) := by decide +kernel
lemma valid_part13_2 : FiniteIntervals.Covers ValidAt 158 159 :=
  FiniteIntervals.of_fin 158 1 valid_sub13_2
lemma valid_sub13_3 : ∀ i : Fin 1, ValidAt (159 + i.val) := by decide +kernel
lemma valid_part13_3 : FiniteIntervals.Covers ValidAt 159 160 :=
  FiniteIntervals.of_fin 159 1 valid_sub13_3
lemma valid_sub13_4 : ∀ i : Fin 1, ValidAt (160 + i.val) := by decide +kernel
lemma valid_part13_4 : FiniteIntervals.Covers ValidAt 160 161 :=
  FiniteIntervals.of_fin 160 1 valid_sub13_4
lemma valid_sub13_5 : ∀ i : Fin 1, ValidAt (161 + i.val) := by decide +kernel
lemma valid_part13_5 : FiniteIntervals.Covers ValidAt 161 162 :=
  FiniteIntervals.of_fin 161 1 valid_sub13_5
lemma valid_sub13_6 : ∀ i : Fin 1, ValidAt (162 + i.val) := by decide +kernel
lemma valid_part13_6 : FiniteIntervals.Covers ValidAt 162 163 :=
  FiniteIntervals.of_fin 162 1 valid_sub13_6
lemma valid_sub13_7 : ∀ i : Fin 1, ValidAt (163 + i.val) := by decide +kernel
lemma valid_part13_7 : FiniteIntervals.Covers ValidAt 163 164 :=
  FiniteIntervals.of_fin 163 1 valid_sub13_7
lemma valid_sub13_8 : ∀ i : Fin 1, ValidAt (164 + i.val) := by decide +kernel
lemma valid_part13_8 : FiniteIntervals.Covers ValidAt 164 165 :=
  FiniteIntervals.of_fin 164 1 valid_sub13_8
lemma valid_sub13_9 : ∀ i : Fin 1, ValidAt (165 + i.val) := by decide +kernel
lemma valid_part13_9 : FiniteIntervals.Covers ValidAt 165 166 :=
  FiniteIntervals.of_fin 165 1 valid_sub13_9
lemma valid_sub13_10 : ∀ i : Fin 1, ValidAt (166 + i.val) := by decide +kernel
lemma valid_part13_10 : FiniteIntervals.Covers ValidAt 166 167 :=
  FiniteIntervals.of_fin 166 1 valid_sub13_10
lemma valid_sub13_11 : ∀ i : Fin 1, ValidAt (167 + i.val) := by decide +kernel
lemma valid_part13_11 : FiniteIntervals.Covers ValidAt 167 168 :=
  FiniteIntervals.of_fin 167 1 valid_sub13_11
lemma valid_interval13 : FiniteIntervals.Covers ValidAt 156 168 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part13_0 (FiniteIntervals.merge valid_part13_1 valid_part13_2)) (FiniteIntervals.merge valid_part13_3 (FiniteIntervals.merge valid_part13_4 valid_part13_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part13_6 (FiniteIntervals.merge valid_part13_7 valid_part13_8)) (FiniteIntervals.merge valid_part13_9 (FiniteIntervals.merge valid_part13_10 valid_part13_11))))
#print axioms valid_interval13
end Erdos184Work.PureSixActions0
