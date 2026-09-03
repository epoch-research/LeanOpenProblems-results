import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub27_0 : ∀ i : Fin 1, ValidAt (324 + i.val) := by decide +kernel
lemma valid_part27_0 : FiniteIntervals.Covers ValidAt 324 325 :=
  FiniteIntervals.of_fin 324 1 valid_sub27_0
lemma valid_sub27_1 : ∀ i : Fin 1, ValidAt (325 + i.val) := by decide +kernel
lemma valid_part27_1 : FiniteIntervals.Covers ValidAt 325 326 :=
  FiniteIntervals.of_fin 325 1 valid_sub27_1
lemma valid_sub27_2 : ∀ i : Fin 1, ValidAt (326 + i.val) := by decide +kernel
lemma valid_part27_2 : FiniteIntervals.Covers ValidAt 326 327 :=
  FiniteIntervals.of_fin 326 1 valid_sub27_2
lemma valid_sub27_3 : ∀ i : Fin 1, ValidAt (327 + i.val) := by decide +kernel
lemma valid_part27_3 : FiniteIntervals.Covers ValidAt 327 328 :=
  FiniteIntervals.of_fin 327 1 valid_sub27_3
lemma valid_sub27_4 : ∀ i : Fin 1, ValidAt (328 + i.val) := by decide +kernel
lemma valid_part27_4 : FiniteIntervals.Covers ValidAt 328 329 :=
  FiniteIntervals.of_fin 328 1 valid_sub27_4
lemma valid_sub27_5 : ∀ i : Fin 1, ValidAt (329 + i.val) := by decide +kernel
lemma valid_part27_5 : FiniteIntervals.Covers ValidAt 329 330 :=
  FiniteIntervals.of_fin 329 1 valid_sub27_5
lemma valid_sub27_6 : ∀ i : Fin 1, ValidAt (330 + i.val) := by decide +kernel
lemma valid_part27_6 : FiniteIntervals.Covers ValidAt 330 331 :=
  FiniteIntervals.of_fin 330 1 valid_sub27_6
lemma valid_sub27_7 : ∀ i : Fin 1, ValidAt (331 + i.val) := by decide +kernel
lemma valid_part27_7 : FiniteIntervals.Covers ValidAt 331 332 :=
  FiniteIntervals.of_fin 331 1 valid_sub27_7
lemma valid_sub27_8 : ∀ i : Fin 1, ValidAt (332 + i.val) := by decide +kernel
lemma valid_part27_8 : FiniteIntervals.Covers ValidAt 332 333 :=
  FiniteIntervals.of_fin 332 1 valid_sub27_8
lemma valid_sub27_9 : ∀ i : Fin 1, ValidAt (333 + i.val) := by decide +kernel
lemma valid_part27_9 : FiniteIntervals.Covers ValidAt 333 334 :=
  FiniteIntervals.of_fin 333 1 valid_sub27_9
lemma valid_sub27_10 : ∀ i : Fin 1, ValidAt (334 + i.val) := by decide +kernel
lemma valid_part27_10 : FiniteIntervals.Covers ValidAt 334 335 :=
  FiniteIntervals.of_fin 334 1 valid_sub27_10
lemma valid_sub27_11 : ∀ i : Fin 1, ValidAt (335 + i.val) := by decide +kernel
lemma valid_part27_11 : FiniteIntervals.Covers ValidAt 335 336 :=
  FiniteIntervals.of_fin 335 1 valid_sub27_11
lemma valid_interval27 : FiniteIntervals.Covers ValidAt 324 336 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part27_0 (FiniteIntervals.merge valid_part27_1 valid_part27_2)) (FiniteIntervals.merge valid_part27_3 (FiniteIntervals.merge valid_part27_4 valid_part27_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part27_6 (FiniteIntervals.merge valid_part27_7 valid_part27_8)) (FiniteIntervals.merge valid_part27_9 (FiniteIntervals.merge valid_part27_10 valid_part27_11))))
#print axioms valid_interval27
end Erdos184Work.PureSixActions0
