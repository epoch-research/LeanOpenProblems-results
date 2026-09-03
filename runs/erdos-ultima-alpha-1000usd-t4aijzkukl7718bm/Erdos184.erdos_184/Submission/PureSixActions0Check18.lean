import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub18_0 : ∀ i : Fin 1, ValidAt (216 + i.val) := by decide +kernel
lemma valid_part18_0 : FiniteIntervals.Covers ValidAt 216 217 :=
  FiniteIntervals.of_fin 216 1 valid_sub18_0
lemma valid_sub18_1 : ∀ i : Fin 1, ValidAt (217 + i.val) := by decide +kernel
lemma valid_part18_1 : FiniteIntervals.Covers ValidAt 217 218 :=
  FiniteIntervals.of_fin 217 1 valid_sub18_1
lemma valid_sub18_2 : ∀ i : Fin 1, ValidAt (218 + i.val) := by decide +kernel
lemma valid_part18_2 : FiniteIntervals.Covers ValidAt 218 219 :=
  FiniteIntervals.of_fin 218 1 valid_sub18_2
lemma valid_sub18_3 : ∀ i : Fin 1, ValidAt (219 + i.val) := by decide +kernel
lemma valid_part18_3 : FiniteIntervals.Covers ValidAt 219 220 :=
  FiniteIntervals.of_fin 219 1 valid_sub18_3
lemma valid_sub18_4 : ∀ i : Fin 1, ValidAt (220 + i.val) := by decide +kernel
lemma valid_part18_4 : FiniteIntervals.Covers ValidAt 220 221 :=
  FiniteIntervals.of_fin 220 1 valid_sub18_4
lemma valid_sub18_5 : ∀ i : Fin 1, ValidAt (221 + i.val) := by decide +kernel
lemma valid_part18_5 : FiniteIntervals.Covers ValidAt 221 222 :=
  FiniteIntervals.of_fin 221 1 valid_sub18_5
lemma valid_sub18_6 : ∀ i : Fin 1, ValidAt (222 + i.val) := by decide +kernel
lemma valid_part18_6 : FiniteIntervals.Covers ValidAt 222 223 :=
  FiniteIntervals.of_fin 222 1 valid_sub18_6
lemma valid_sub18_7 : ∀ i : Fin 1, ValidAt (223 + i.val) := by decide +kernel
lemma valid_part18_7 : FiniteIntervals.Covers ValidAt 223 224 :=
  FiniteIntervals.of_fin 223 1 valid_sub18_7
lemma valid_sub18_8 : ∀ i : Fin 1, ValidAt (224 + i.val) := by decide +kernel
lemma valid_part18_8 : FiniteIntervals.Covers ValidAt 224 225 :=
  FiniteIntervals.of_fin 224 1 valid_sub18_8
lemma valid_sub18_9 : ∀ i : Fin 1, ValidAt (225 + i.val) := by decide +kernel
lemma valid_part18_9 : FiniteIntervals.Covers ValidAt 225 226 :=
  FiniteIntervals.of_fin 225 1 valid_sub18_9
lemma valid_sub18_10 : ∀ i : Fin 1, ValidAt (226 + i.val) := by decide +kernel
lemma valid_part18_10 : FiniteIntervals.Covers ValidAt 226 227 :=
  FiniteIntervals.of_fin 226 1 valid_sub18_10
lemma valid_sub18_11 : ∀ i : Fin 1, ValidAt (227 + i.val) := by decide +kernel
lemma valid_part18_11 : FiniteIntervals.Covers ValidAt 227 228 :=
  FiniteIntervals.of_fin 227 1 valid_sub18_11
lemma valid_interval18 : FiniteIntervals.Covers ValidAt 216 228 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part18_0 (FiniteIntervals.merge valid_part18_1 valid_part18_2)) (FiniteIntervals.merge valid_part18_3 (FiniteIntervals.merge valid_part18_4 valid_part18_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part18_6 (FiniteIntervals.merge valid_part18_7 valid_part18_8)) (FiniteIntervals.merge valid_part18_9 (FiniteIntervals.merge valid_part18_10 valid_part18_11))))
#print axioms valid_interval18
end Erdos184Work.PureSixActions0
