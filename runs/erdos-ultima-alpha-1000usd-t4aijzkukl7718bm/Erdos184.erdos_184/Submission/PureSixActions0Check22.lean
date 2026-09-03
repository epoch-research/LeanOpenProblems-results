import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub22_0 : ∀ i : Fin 1, ValidAt (264 + i.val) := by decide +kernel
lemma valid_part22_0 : FiniteIntervals.Covers ValidAt 264 265 :=
  FiniteIntervals.of_fin 264 1 valid_sub22_0
lemma valid_sub22_1 : ∀ i : Fin 1, ValidAt (265 + i.val) := by decide +kernel
lemma valid_part22_1 : FiniteIntervals.Covers ValidAt 265 266 :=
  FiniteIntervals.of_fin 265 1 valid_sub22_1
lemma valid_sub22_2 : ∀ i : Fin 1, ValidAt (266 + i.val) := by decide +kernel
lemma valid_part22_2 : FiniteIntervals.Covers ValidAt 266 267 :=
  FiniteIntervals.of_fin 266 1 valid_sub22_2
lemma valid_sub22_3 : ∀ i : Fin 1, ValidAt (267 + i.val) := by decide +kernel
lemma valid_part22_3 : FiniteIntervals.Covers ValidAt 267 268 :=
  FiniteIntervals.of_fin 267 1 valid_sub22_3
lemma valid_sub22_4 : ∀ i : Fin 1, ValidAt (268 + i.val) := by decide +kernel
lemma valid_part22_4 : FiniteIntervals.Covers ValidAt 268 269 :=
  FiniteIntervals.of_fin 268 1 valid_sub22_4
lemma valid_sub22_5 : ∀ i : Fin 1, ValidAt (269 + i.val) := by decide +kernel
lemma valid_part22_5 : FiniteIntervals.Covers ValidAt 269 270 :=
  FiniteIntervals.of_fin 269 1 valid_sub22_5
lemma valid_sub22_6 : ∀ i : Fin 1, ValidAt (270 + i.val) := by decide +kernel
lemma valid_part22_6 : FiniteIntervals.Covers ValidAt 270 271 :=
  FiniteIntervals.of_fin 270 1 valid_sub22_6
lemma valid_sub22_7 : ∀ i : Fin 1, ValidAt (271 + i.val) := by decide +kernel
lemma valid_part22_7 : FiniteIntervals.Covers ValidAt 271 272 :=
  FiniteIntervals.of_fin 271 1 valid_sub22_7
lemma valid_sub22_8 : ∀ i : Fin 1, ValidAt (272 + i.val) := by decide +kernel
lemma valid_part22_8 : FiniteIntervals.Covers ValidAt 272 273 :=
  FiniteIntervals.of_fin 272 1 valid_sub22_8
lemma valid_sub22_9 : ∀ i : Fin 1, ValidAt (273 + i.val) := by decide +kernel
lemma valid_part22_9 : FiniteIntervals.Covers ValidAt 273 274 :=
  FiniteIntervals.of_fin 273 1 valid_sub22_9
lemma valid_sub22_10 : ∀ i : Fin 1, ValidAt (274 + i.val) := by decide +kernel
lemma valid_part22_10 : FiniteIntervals.Covers ValidAt 274 275 :=
  FiniteIntervals.of_fin 274 1 valid_sub22_10
lemma valid_sub22_11 : ∀ i : Fin 1, ValidAt (275 + i.val) := by decide +kernel
lemma valid_part22_11 : FiniteIntervals.Covers ValidAt 275 276 :=
  FiniteIntervals.of_fin 275 1 valid_sub22_11
lemma valid_interval22 : FiniteIntervals.Covers ValidAt 264 276 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part22_0 (FiniteIntervals.merge valid_part22_1 valid_part22_2)) (FiniteIntervals.merge valid_part22_3 (FiniteIntervals.merge valid_part22_4 valid_part22_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part22_6 (FiniteIntervals.merge valid_part22_7 valid_part22_8)) (FiniteIntervals.merge valid_part22_9 (FiniteIntervals.merge valid_part22_10 valid_part22_11))))
#print axioms valid_interval22
end Erdos184Work.PureSixActions0
