import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub25_0 : ∀ i : Fin 1, ValidAt (300 + i.val) := by decide +kernel
lemma valid_part25_0 : FiniteIntervals.Covers ValidAt 300 301 :=
  FiniteIntervals.of_fin 300 1 valid_sub25_0
lemma valid_sub25_1 : ∀ i : Fin 1, ValidAt (301 + i.val) := by decide +kernel
lemma valid_part25_1 : FiniteIntervals.Covers ValidAt 301 302 :=
  FiniteIntervals.of_fin 301 1 valid_sub25_1
lemma valid_sub25_2 : ∀ i : Fin 1, ValidAt (302 + i.val) := by decide +kernel
lemma valid_part25_2 : FiniteIntervals.Covers ValidAt 302 303 :=
  FiniteIntervals.of_fin 302 1 valid_sub25_2
lemma valid_sub25_3 : ∀ i : Fin 1, ValidAt (303 + i.val) := by decide +kernel
lemma valid_part25_3 : FiniteIntervals.Covers ValidAt 303 304 :=
  FiniteIntervals.of_fin 303 1 valid_sub25_3
lemma valid_sub25_4 : ∀ i : Fin 1, ValidAt (304 + i.val) := by decide +kernel
lemma valid_part25_4 : FiniteIntervals.Covers ValidAt 304 305 :=
  FiniteIntervals.of_fin 304 1 valid_sub25_4
lemma valid_sub25_5 : ∀ i : Fin 1, ValidAt (305 + i.val) := by decide +kernel
lemma valid_part25_5 : FiniteIntervals.Covers ValidAt 305 306 :=
  FiniteIntervals.of_fin 305 1 valid_sub25_5
lemma valid_sub25_6 : ∀ i : Fin 1, ValidAt (306 + i.val) := by decide +kernel
lemma valid_part25_6 : FiniteIntervals.Covers ValidAt 306 307 :=
  FiniteIntervals.of_fin 306 1 valid_sub25_6
lemma valid_sub25_7 : ∀ i : Fin 1, ValidAt (307 + i.val) := by decide +kernel
lemma valid_part25_7 : FiniteIntervals.Covers ValidAt 307 308 :=
  FiniteIntervals.of_fin 307 1 valid_sub25_7
lemma valid_sub25_8 : ∀ i : Fin 1, ValidAt (308 + i.val) := by decide +kernel
lemma valid_part25_8 : FiniteIntervals.Covers ValidAt 308 309 :=
  FiniteIntervals.of_fin 308 1 valid_sub25_8
lemma valid_sub25_9 : ∀ i : Fin 1, ValidAt (309 + i.val) := by decide +kernel
lemma valid_part25_9 : FiniteIntervals.Covers ValidAt 309 310 :=
  FiniteIntervals.of_fin 309 1 valid_sub25_9
lemma valid_sub25_10 : ∀ i : Fin 1, ValidAt (310 + i.val) := by decide +kernel
lemma valid_part25_10 : FiniteIntervals.Covers ValidAt 310 311 :=
  FiniteIntervals.of_fin 310 1 valid_sub25_10
lemma valid_sub25_11 : ∀ i : Fin 1, ValidAt (311 + i.val) := by decide +kernel
lemma valid_part25_11 : FiniteIntervals.Covers ValidAt 311 312 :=
  FiniteIntervals.of_fin 311 1 valid_sub25_11
lemma valid_interval25 : FiniteIntervals.Covers ValidAt 300 312 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part25_0 (FiniteIntervals.merge valid_part25_1 valid_part25_2)) (FiniteIntervals.merge valid_part25_3 (FiniteIntervals.merge valid_part25_4 valid_part25_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part25_6 (FiniteIntervals.merge valid_part25_7 valid_part25_8)) (FiniteIntervals.merge valid_part25_9 (FiniteIntervals.merge valid_part25_10 valid_part25_11))))
#print axioms valid_interval25
end Erdos184Work.PureSixActions0
