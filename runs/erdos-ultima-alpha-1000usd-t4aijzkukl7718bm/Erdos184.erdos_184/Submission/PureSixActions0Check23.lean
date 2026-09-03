import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub23_0 : ∀ i : Fin 1, ValidAt (276 + i.val) := by decide +kernel
lemma valid_part23_0 : FiniteIntervals.Covers ValidAt 276 277 :=
  FiniteIntervals.of_fin 276 1 valid_sub23_0
lemma valid_sub23_1 : ∀ i : Fin 1, ValidAt (277 + i.val) := by decide +kernel
lemma valid_part23_1 : FiniteIntervals.Covers ValidAt 277 278 :=
  FiniteIntervals.of_fin 277 1 valid_sub23_1
lemma valid_sub23_2 : ∀ i : Fin 1, ValidAt (278 + i.val) := by decide +kernel
lemma valid_part23_2 : FiniteIntervals.Covers ValidAt 278 279 :=
  FiniteIntervals.of_fin 278 1 valid_sub23_2
lemma valid_sub23_3 : ∀ i : Fin 1, ValidAt (279 + i.val) := by decide +kernel
lemma valid_part23_3 : FiniteIntervals.Covers ValidAt 279 280 :=
  FiniteIntervals.of_fin 279 1 valid_sub23_3
lemma valid_sub23_4 : ∀ i : Fin 1, ValidAt (280 + i.val) := by decide +kernel
lemma valid_part23_4 : FiniteIntervals.Covers ValidAt 280 281 :=
  FiniteIntervals.of_fin 280 1 valid_sub23_4
lemma valid_sub23_5 : ∀ i : Fin 1, ValidAt (281 + i.val) := by decide +kernel
lemma valid_part23_5 : FiniteIntervals.Covers ValidAt 281 282 :=
  FiniteIntervals.of_fin 281 1 valid_sub23_5
lemma valid_sub23_6 : ∀ i : Fin 1, ValidAt (282 + i.val) := by decide +kernel
lemma valid_part23_6 : FiniteIntervals.Covers ValidAt 282 283 :=
  FiniteIntervals.of_fin 282 1 valid_sub23_6
lemma valid_sub23_7 : ∀ i : Fin 1, ValidAt (283 + i.val) := by decide +kernel
lemma valid_part23_7 : FiniteIntervals.Covers ValidAt 283 284 :=
  FiniteIntervals.of_fin 283 1 valid_sub23_7
lemma valid_sub23_8 : ∀ i : Fin 1, ValidAt (284 + i.val) := by decide +kernel
lemma valid_part23_8 : FiniteIntervals.Covers ValidAt 284 285 :=
  FiniteIntervals.of_fin 284 1 valid_sub23_8
lemma valid_sub23_9 : ∀ i : Fin 1, ValidAt (285 + i.val) := by decide +kernel
lemma valid_part23_9 : FiniteIntervals.Covers ValidAt 285 286 :=
  FiniteIntervals.of_fin 285 1 valid_sub23_9
lemma valid_sub23_10 : ∀ i : Fin 1, ValidAt (286 + i.val) := by decide +kernel
lemma valid_part23_10 : FiniteIntervals.Covers ValidAt 286 287 :=
  FiniteIntervals.of_fin 286 1 valid_sub23_10
lemma valid_sub23_11 : ∀ i : Fin 1, ValidAt (287 + i.val) := by decide +kernel
lemma valid_part23_11 : FiniteIntervals.Covers ValidAt 287 288 :=
  FiniteIntervals.of_fin 287 1 valid_sub23_11
lemma valid_interval23 : FiniteIntervals.Covers ValidAt 276 288 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part23_0 (FiniteIntervals.merge valid_part23_1 valid_part23_2)) (FiniteIntervals.merge valid_part23_3 (FiniteIntervals.merge valid_part23_4 valid_part23_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part23_6 (FiniteIntervals.merge valid_part23_7 valid_part23_8)) (FiniteIntervals.merge valid_part23_9 (FiniteIntervals.merge valid_part23_10 valid_part23_11))))
#print axioms valid_interval23
end Erdos184Work.PureSixActions0
