import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub3_0 : ∀ i : Fin 1, ValidAt (36 + i.val) := by decide +kernel
lemma valid_part3_0 : FiniteIntervals.Covers ValidAt 36 37 :=
  FiniteIntervals.of_fin 36 1 valid_sub3_0
lemma valid_sub3_1 : ∀ i : Fin 1, ValidAt (37 + i.val) := by decide +kernel
lemma valid_part3_1 : FiniteIntervals.Covers ValidAt 37 38 :=
  FiniteIntervals.of_fin 37 1 valid_sub3_1
lemma valid_sub3_2 : ∀ i : Fin 1, ValidAt (38 + i.val) := by decide +kernel
lemma valid_part3_2 : FiniteIntervals.Covers ValidAt 38 39 :=
  FiniteIntervals.of_fin 38 1 valid_sub3_2
lemma valid_sub3_3 : ∀ i : Fin 1, ValidAt (39 + i.val) := by decide +kernel
lemma valid_part3_3 : FiniteIntervals.Covers ValidAt 39 40 :=
  FiniteIntervals.of_fin 39 1 valid_sub3_3
lemma valid_sub3_4 : ∀ i : Fin 1, ValidAt (40 + i.val) := by decide +kernel
lemma valid_part3_4 : FiniteIntervals.Covers ValidAt 40 41 :=
  FiniteIntervals.of_fin 40 1 valid_sub3_4
lemma valid_sub3_5 : ∀ i : Fin 1, ValidAt (41 + i.val) := by decide +kernel
lemma valid_part3_5 : FiniteIntervals.Covers ValidAt 41 42 :=
  FiniteIntervals.of_fin 41 1 valid_sub3_5
lemma valid_sub3_6 : ∀ i : Fin 1, ValidAt (42 + i.val) := by decide +kernel
lemma valid_part3_6 : FiniteIntervals.Covers ValidAt 42 43 :=
  FiniteIntervals.of_fin 42 1 valid_sub3_6
lemma valid_sub3_7 : ∀ i : Fin 1, ValidAt (43 + i.val) := by decide +kernel
lemma valid_part3_7 : FiniteIntervals.Covers ValidAt 43 44 :=
  FiniteIntervals.of_fin 43 1 valid_sub3_7
lemma valid_sub3_8 : ∀ i : Fin 1, ValidAt (44 + i.val) := by decide +kernel
lemma valid_part3_8 : FiniteIntervals.Covers ValidAt 44 45 :=
  FiniteIntervals.of_fin 44 1 valid_sub3_8
lemma valid_sub3_9 : ∀ i : Fin 1, ValidAt (45 + i.val) := by decide +kernel
lemma valid_part3_9 : FiniteIntervals.Covers ValidAt 45 46 :=
  FiniteIntervals.of_fin 45 1 valid_sub3_9
lemma valid_sub3_10 : ∀ i : Fin 1, ValidAt (46 + i.val) := by decide +kernel
lemma valid_part3_10 : FiniteIntervals.Covers ValidAt 46 47 :=
  FiniteIntervals.of_fin 46 1 valid_sub3_10
lemma valid_sub3_11 : ∀ i : Fin 1, ValidAt (47 + i.val) := by decide +kernel
lemma valid_part3_11 : FiniteIntervals.Covers ValidAt 47 48 :=
  FiniteIntervals.of_fin 47 1 valid_sub3_11
lemma valid_interval3 : FiniteIntervals.Covers ValidAt 36 48 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part3_0 (FiniteIntervals.merge valid_part3_1 valid_part3_2)) (FiniteIntervals.merge valid_part3_3 (FiniteIntervals.merge valid_part3_4 valid_part3_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part3_6 (FiniteIntervals.merge valid_part3_7 valid_part3_8)) (FiniteIntervals.merge valid_part3_9 (FiniteIntervals.merge valid_part3_10 valid_part3_11))))
#print axioms valid_interval3
end Erdos184Work.PureSixActions0
