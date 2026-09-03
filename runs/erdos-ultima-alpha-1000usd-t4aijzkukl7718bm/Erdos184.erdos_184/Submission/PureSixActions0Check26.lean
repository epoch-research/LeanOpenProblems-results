import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub26_0 : ∀ i : Fin 1, ValidAt (312 + i.val) := by decide +kernel
lemma valid_part26_0 : FiniteIntervals.Covers ValidAt 312 313 :=
  FiniteIntervals.of_fin 312 1 valid_sub26_0
lemma valid_sub26_1 : ∀ i : Fin 1, ValidAt (313 + i.val) := by decide +kernel
lemma valid_part26_1 : FiniteIntervals.Covers ValidAt 313 314 :=
  FiniteIntervals.of_fin 313 1 valid_sub26_1
lemma valid_sub26_2 : ∀ i : Fin 1, ValidAt (314 + i.val) := by decide +kernel
lemma valid_part26_2 : FiniteIntervals.Covers ValidAt 314 315 :=
  FiniteIntervals.of_fin 314 1 valid_sub26_2
lemma valid_sub26_3 : ∀ i : Fin 1, ValidAt (315 + i.val) := by decide +kernel
lemma valid_part26_3 : FiniteIntervals.Covers ValidAt 315 316 :=
  FiniteIntervals.of_fin 315 1 valid_sub26_3
lemma valid_sub26_4 : ∀ i : Fin 1, ValidAt (316 + i.val) := by decide +kernel
lemma valid_part26_4 : FiniteIntervals.Covers ValidAt 316 317 :=
  FiniteIntervals.of_fin 316 1 valid_sub26_4
lemma valid_sub26_5 : ∀ i : Fin 1, ValidAt (317 + i.val) := by decide +kernel
lemma valid_part26_5 : FiniteIntervals.Covers ValidAt 317 318 :=
  FiniteIntervals.of_fin 317 1 valid_sub26_5
lemma valid_sub26_6 : ∀ i : Fin 1, ValidAt (318 + i.val) := by decide +kernel
lemma valid_part26_6 : FiniteIntervals.Covers ValidAt 318 319 :=
  FiniteIntervals.of_fin 318 1 valid_sub26_6
lemma valid_sub26_7 : ∀ i : Fin 1, ValidAt (319 + i.val) := by decide +kernel
lemma valid_part26_7 : FiniteIntervals.Covers ValidAt 319 320 :=
  FiniteIntervals.of_fin 319 1 valid_sub26_7
lemma valid_sub26_8 : ∀ i : Fin 1, ValidAt (320 + i.val) := by decide +kernel
lemma valid_part26_8 : FiniteIntervals.Covers ValidAt 320 321 :=
  FiniteIntervals.of_fin 320 1 valid_sub26_8
lemma valid_sub26_9 : ∀ i : Fin 1, ValidAt (321 + i.val) := by decide +kernel
lemma valid_part26_9 : FiniteIntervals.Covers ValidAt 321 322 :=
  FiniteIntervals.of_fin 321 1 valid_sub26_9
lemma valid_sub26_10 : ∀ i : Fin 1, ValidAt (322 + i.val) := by decide +kernel
lemma valid_part26_10 : FiniteIntervals.Covers ValidAt 322 323 :=
  FiniteIntervals.of_fin 322 1 valid_sub26_10
lemma valid_sub26_11 : ∀ i : Fin 1, ValidAt (323 + i.val) := by decide +kernel
lemma valid_part26_11 : FiniteIntervals.Covers ValidAt 323 324 :=
  FiniteIntervals.of_fin 323 1 valid_sub26_11
lemma valid_interval26 : FiniteIntervals.Covers ValidAt 312 324 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part26_0 (FiniteIntervals.merge valid_part26_1 valid_part26_2)) (FiniteIntervals.merge valid_part26_3 (FiniteIntervals.merge valid_part26_4 valid_part26_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part26_6 (FiniteIntervals.merge valid_part26_7 valid_part26_8)) (FiniteIntervals.merge valid_part26_9 (FiniteIntervals.merge valid_part26_10 valid_part26_11))))
#print axioms valid_interval26
end Erdos184Work.PureSixActions0
