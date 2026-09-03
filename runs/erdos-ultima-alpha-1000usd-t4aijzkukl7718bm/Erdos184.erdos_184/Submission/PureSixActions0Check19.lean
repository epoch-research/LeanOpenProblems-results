import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub19_0 : ∀ i : Fin 1, ValidAt (228 + i.val) := by decide +kernel
lemma valid_part19_0 : FiniteIntervals.Covers ValidAt 228 229 :=
  FiniteIntervals.of_fin 228 1 valid_sub19_0
lemma valid_sub19_1 : ∀ i : Fin 1, ValidAt (229 + i.val) := by decide +kernel
lemma valid_part19_1 : FiniteIntervals.Covers ValidAt 229 230 :=
  FiniteIntervals.of_fin 229 1 valid_sub19_1
lemma valid_sub19_2 : ∀ i : Fin 1, ValidAt (230 + i.val) := by decide +kernel
lemma valid_part19_2 : FiniteIntervals.Covers ValidAt 230 231 :=
  FiniteIntervals.of_fin 230 1 valid_sub19_2
lemma valid_sub19_3 : ∀ i : Fin 1, ValidAt (231 + i.val) := by decide +kernel
lemma valid_part19_3 : FiniteIntervals.Covers ValidAt 231 232 :=
  FiniteIntervals.of_fin 231 1 valid_sub19_3
lemma valid_sub19_4 : ∀ i : Fin 1, ValidAt (232 + i.val) := by decide +kernel
lemma valid_part19_4 : FiniteIntervals.Covers ValidAt 232 233 :=
  FiniteIntervals.of_fin 232 1 valid_sub19_4
lemma valid_sub19_5 : ∀ i : Fin 1, ValidAt (233 + i.val) := by decide +kernel
lemma valid_part19_5 : FiniteIntervals.Covers ValidAt 233 234 :=
  FiniteIntervals.of_fin 233 1 valid_sub19_5
lemma valid_sub19_6 : ∀ i : Fin 1, ValidAt (234 + i.val) := by decide +kernel
lemma valid_part19_6 : FiniteIntervals.Covers ValidAt 234 235 :=
  FiniteIntervals.of_fin 234 1 valid_sub19_6
lemma valid_sub19_7 : ∀ i : Fin 1, ValidAt (235 + i.val) := by decide +kernel
lemma valid_part19_7 : FiniteIntervals.Covers ValidAt 235 236 :=
  FiniteIntervals.of_fin 235 1 valid_sub19_7
lemma valid_sub19_8 : ∀ i : Fin 1, ValidAt (236 + i.val) := by decide +kernel
lemma valid_part19_8 : FiniteIntervals.Covers ValidAt 236 237 :=
  FiniteIntervals.of_fin 236 1 valid_sub19_8
lemma valid_sub19_9 : ∀ i : Fin 1, ValidAt (237 + i.val) := by decide +kernel
lemma valid_part19_9 : FiniteIntervals.Covers ValidAt 237 238 :=
  FiniteIntervals.of_fin 237 1 valid_sub19_9
lemma valid_sub19_10 : ∀ i : Fin 1, ValidAt (238 + i.val) := by decide +kernel
lemma valid_part19_10 : FiniteIntervals.Covers ValidAt 238 239 :=
  FiniteIntervals.of_fin 238 1 valid_sub19_10
lemma valid_sub19_11 : ∀ i : Fin 1, ValidAt (239 + i.val) := by decide +kernel
lemma valid_part19_11 : FiniteIntervals.Covers ValidAt 239 240 :=
  FiniteIntervals.of_fin 239 1 valid_sub19_11
lemma valid_interval19 : FiniteIntervals.Covers ValidAt 228 240 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part19_0 (FiniteIntervals.merge valid_part19_1 valid_part19_2)) (FiniteIntervals.merge valid_part19_3 (FiniteIntervals.merge valid_part19_4 valid_part19_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part19_6 (FiniteIntervals.merge valid_part19_7 valid_part19_8)) (FiniteIntervals.merge valid_part19_9 (FiniteIntervals.merge valid_part19_10 valid_part19_11))))
#print axioms valid_interval19
end Erdos184Work.PureSixActions0
