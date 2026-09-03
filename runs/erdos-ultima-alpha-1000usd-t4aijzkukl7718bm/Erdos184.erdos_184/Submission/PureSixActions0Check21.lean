import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub21_0 : ∀ i : Fin 1, ValidAt (252 + i.val) := by decide +kernel
lemma valid_part21_0 : FiniteIntervals.Covers ValidAt 252 253 :=
  FiniteIntervals.of_fin 252 1 valid_sub21_0
lemma valid_sub21_1 : ∀ i : Fin 1, ValidAt (253 + i.val) := by decide +kernel
lemma valid_part21_1 : FiniteIntervals.Covers ValidAt 253 254 :=
  FiniteIntervals.of_fin 253 1 valid_sub21_1
lemma valid_sub21_2 : ∀ i : Fin 1, ValidAt (254 + i.val) := by decide +kernel
lemma valid_part21_2 : FiniteIntervals.Covers ValidAt 254 255 :=
  FiniteIntervals.of_fin 254 1 valid_sub21_2
lemma valid_sub21_3 : ∀ i : Fin 1, ValidAt (255 + i.val) := by decide +kernel
lemma valid_part21_3 : FiniteIntervals.Covers ValidAt 255 256 :=
  FiniteIntervals.of_fin 255 1 valid_sub21_3
lemma valid_sub21_4 : ∀ i : Fin 1, ValidAt (256 + i.val) := by decide +kernel
lemma valid_part21_4 : FiniteIntervals.Covers ValidAt 256 257 :=
  FiniteIntervals.of_fin 256 1 valid_sub21_4
lemma valid_sub21_5 : ∀ i : Fin 1, ValidAt (257 + i.val) := by decide +kernel
lemma valid_part21_5 : FiniteIntervals.Covers ValidAt 257 258 :=
  FiniteIntervals.of_fin 257 1 valid_sub21_5
lemma valid_sub21_6 : ∀ i : Fin 1, ValidAt (258 + i.val) := by decide +kernel
lemma valid_part21_6 : FiniteIntervals.Covers ValidAt 258 259 :=
  FiniteIntervals.of_fin 258 1 valid_sub21_6
lemma valid_sub21_7 : ∀ i : Fin 1, ValidAt (259 + i.val) := by decide +kernel
lemma valid_part21_7 : FiniteIntervals.Covers ValidAt 259 260 :=
  FiniteIntervals.of_fin 259 1 valid_sub21_7
lemma valid_sub21_8 : ∀ i : Fin 1, ValidAt (260 + i.val) := by decide +kernel
lemma valid_part21_8 : FiniteIntervals.Covers ValidAt 260 261 :=
  FiniteIntervals.of_fin 260 1 valid_sub21_8
lemma valid_sub21_9 : ∀ i : Fin 1, ValidAt (261 + i.val) := by decide +kernel
lemma valid_part21_9 : FiniteIntervals.Covers ValidAt 261 262 :=
  FiniteIntervals.of_fin 261 1 valid_sub21_9
lemma valid_sub21_10 : ∀ i : Fin 1, ValidAt (262 + i.val) := by decide +kernel
lemma valid_part21_10 : FiniteIntervals.Covers ValidAt 262 263 :=
  FiniteIntervals.of_fin 262 1 valid_sub21_10
lemma valid_sub21_11 : ∀ i : Fin 1, ValidAt (263 + i.val) := by decide +kernel
lemma valid_part21_11 : FiniteIntervals.Covers ValidAt 263 264 :=
  FiniteIntervals.of_fin 263 1 valid_sub21_11
lemma valid_interval21 : FiniteIntervals.Covers ValidAt 252 264 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part21_0 (FiniteIntervals.merge valid_part21_1 valid_part21_2)) (FiniteIntervals.merge valid_part21_3 (FiniteIntervals.merge valid_part21_4 valid_part21_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part21_6 (FiniteIntervals.merge valid_part21_7 valid_part21_8)) (FiniteIntervals.merge valid_part21_9 (FiniteIntervals.merge valid_part21_10 valid_part21_11))))
#print axioms valid_interval21
end Erdos184Work.PureSixActions0
