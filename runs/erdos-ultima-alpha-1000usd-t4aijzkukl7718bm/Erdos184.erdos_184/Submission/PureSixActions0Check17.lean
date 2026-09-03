import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub17_0 : ∀ i : Fin 1, ValidAt (204 + i.val) := by decide +kernel
lemma valid_part17_0 : FiniteIntervals.Covers ValidAt 204 205 :=
  FiniteIntervals.of_fin 204 1 valid_sub17_0
lemma valid_sub17_1 : ∀ i : Fin 1, ValidAt (205 + i.val) := by decide +kernel
lemma valid_part17_1 : FiniteIntervals.Covers ValidAt 205 206 :=
  FiniteIntervals.of_fin 205 1 valid_sub17_1
lemma valid_sub17_2 : ∀ i : Fin 1, ValidAt (206 + i.val) := by decide +kernel
lemma valid_part17_2 : FiniteIntervals.Covers ValidAt 206 207 :=
  FiniteIntervals.of_fin 206 1 valid_sub17_2
lemma valid_sub17_3 : ∀ i : Fin 1, ValidAt (207 + i.val) := by decide +kernel
lemma valid_part17_3 : FiniteIntervals.Covers ValidAt 207 208 :=
  FiniteIntervals.of_fin 207 1 valid_sub17_3
lemma valid_sub17_4 : ∀ i : Fin 1, ValidAt (208 + i.val) := by decide +kernel
lemma valid_part17_4 : FiniteIntervals.Covers ValidAt 208 209 :=
  FiniteIntervals.of_fin 208 1 valid_sub17_4
lemma valid_sub17_5 : ∀ i : Fin 1, ValidAt (209 + i.val) := by decide +kernel
lemma valid_part17_5 : FiniteIntervals.Covers ValidAt 209 210 :=
  FiniteIntervals.of_fin 209 1 valid_sub17_5
lemma valid_sub17_6 : ∀ i : Fin 1, ValidAt (210 + i.val) := by decide +kernel
lemma valid_part17_6 : FiniteIntervals.Covers ValidAt 210 211 :=
  FiniteIntervals.of_fin 210 1 valid_sub17_6
lemma valid_sub17_7 : ∀ i : Fin 1, ValidAt (211 + i.val) := by decide +kernel
lemma valid_part17_7 : FiniteIntervals.Covers ValidAt 211 212 :=
  FiniteIntervals.of_fin 211 1 valid_sub17_7
lemma valid_sub17_8 : ∀ i : Fin 1, ValidAt (212 + i.val) := by decide +kernel
lemma valid_part17_8 : FiniteIntervals.Covers ValidAt 212 213 :=
  FiniteIntervals.of_fin 212 1 valid_sub17_8
lemma valid_sub17_9 : ∀ i : Fin 1, ValidAt (213 + i.val) := by decide +kernel
lemma valid_part17_9 : FiniteIntervals.Covers ValidAt 213 214 :=
  FiniteIntervals.of_fin 213 1 valid_sub17_9
lemma valid_sub17_10 : ∀ i : Fin 1, ValidAt (214 + i.val) := by decide +kernel
lemma valid_part17_10 : FiniteIntervals.Covers ValidAt 214 215 :=
  FiniteIntervals.of_fin 214 1 valid_sub17_10
lemma valid_sub17_11 : ∀ i : Fin 1, ValidAt (215 + i.val) := by decide +kernel
lemma valid_part17_11 : FiniteIntervals.Covers ValidAt 215 216 :=
  FiniteIntervals.of_fin 215 1 valid_sub17_11
lemma valid_interval17 : FiniteIntervals.Covers ValidAt 204 216 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part17_0 (FiniteIntervals.merge valid_part17_1 valid_part17_2)) (FiniteIntervals.merge valid_part17_3 (FiniteIntervals.merge valid_part17_4 valid_part17_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part17_6 (FiniteIntervals.merge valid_part17_7 valid_part17_8)) (FiniteIntervals.merge valid_part17_9 (FiniteIntervals.merge valid_part17_10 valid_part17_11))))
#print axioms valid_interval17
end Erdos184Work.PureSixActions0
