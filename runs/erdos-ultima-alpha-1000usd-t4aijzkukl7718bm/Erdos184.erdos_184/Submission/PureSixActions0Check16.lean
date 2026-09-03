import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub16_0 : ∀ i : Fin 1, ValidAt (192 + i.val) := by decide +kernel
lemma valid_part16_0 : FiniteIntervals.Covers ValidAt 192 193 :=
  FiniteIntervals.of_fin 192 1 valid_sub16_0
lemma valid_sub16_1 : ∀ i : Fin 1, ValidAt (193 + i.val) := by decide +kernel
lemma valid_part16_1 : FiniteIntervals.Covers ValidAt 193 194 :=
  FiniteIntervals.of_fin 193 1 valid_sub16_1
lemma valid_sub16_2 : ∀ i : Fin 1, ValidAt (194 + i.val) := by decide +kernel
lemma valid_part16_2 : FiniteIntervals.Covers ValidAt 194 195 :=
  FiniteIntervals.of_fin 194 1 valid_sub16_2
lemma valid_sub16_3 : ∀ i : Fin 1, ValidAt (195 + i.val) := by decide +kernel
lemma valid_part16_3 : FiniteIntervals.Covers ValidAt 195 196 :=
  FiniteIntervals.of_fin 195 1 valid_sub16_3
lemma valid_sub16_4 : ∀ i : Fin 1, ValidAt (196 + i.val) := by decide +kernel
lemma valid_part16_4 : FiniteIntervals.Covers ValidAt 196 197 :=
  FiniteIntervals.of_fin 196 1 valid_sub16_4
lemma valid_sub16_5 : ∀ i : Fin 1, ValidAt (197 + i.val) := by decide +kernel
lemma valid_part16_5 : FiniteIntervals.Covers ValidAt 197 198 :=
  FiniteIntervals.of_fin 197 1 valid_sub16_5
lemma valid_sub16_6 : ∀ i : Fin 1, ValidAt (198 + i.val) := by decide +kernel
lemma valid_part16_6 : FiniteIntervals.Covers ValidAt 198 199 :=
  FiniteIntervals.of_fin 198 1 valid_sub16_6
lemma valid_sub16_7 : ∀ i : Fin 1, ValidAt (199 + i.val) := by decide +kernel
lemma valid_part16_7 : FiniteIntervals.Covers ValidAt 199 200 :=
  FiniteIntervals.of_fin 199 1 valid_sub16_7
lemma valid_sub16_8 : ∀ i : Fin 1, ValidAt (200 + i.val) := by decide +kernel
lemma valid_part16_8 : FiniteIntervals.Covers ValidAt 200 201 :=
  FiniteIntervals.of_fin 200 1 valid_sub16_8
lemma valid_sub16_9 : ∀ i : Fin 1, ValidAt (201 + i.val) := by decide +kernel
lemma valid_part16_9 : FiniteIntervals.Covers ValidAt 201 202 :=
  FiniteIntervals.of_fin 201 1 valid_sub16_9
lemma valid_sub16_10 : ∀ i : Fin 1, ValidAt (202 + i.val) := by decide +kernel
lemma valid_part16_10 : FiniteIntervals.Covers ValidAt 202 203 :=
  FiniteIntervals.of_fin 202 1 valid_sub16_10
lemma valid_sub16_11 : ∀ i : Fin 1, ValidAt (203 + i.val) := by decide +kernel
lemma valid_part16_11 : FiniteIntervals.Covers ValidAt 203 204 :=
  FiniteIntervals.of_fin 203 1 valid_sub16_11
lemma valid_interval16 : FiniteIntervals.Covers ValidAt 192 204 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part16_0 (FiniteIntervals.merge valid_part16_1 valid_part16_2)) (FiniteIntervals.merge valid_part16_3 (FiniteIntervals.merge valid_part16_4 valid_part16_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part16_6 (FiniteIntervals.merge valid_part16_7 valid_part16_8)) (FiniteIntervals.merge valid_part16_9 (FiniteIntervals.merge valid_part16_10 valid_part16_11))))
#print axioms valid_interval16
end Erdos184Work.PureSixActions0
