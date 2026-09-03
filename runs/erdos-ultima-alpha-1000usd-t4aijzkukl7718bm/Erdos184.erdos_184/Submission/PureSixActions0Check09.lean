import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub9_0 : ∀ i : Fin 1, ValidAt (108 + i.val) := by decide +kernel
lemma valid_part9_0 : FiniteIntervals.Covers ValidAt 108 109 :=
  FiniteIntervals.of_fin 108 1 valid_sub9_0
lemma valid_sub9_1 : ∀ i : Fin 1, ValidAt (109 + i.val) := by decide +kernel
lemma valid_part9_1 : FiniteIntervals.Covers ValidAt 109 110 :=
  FiniteIntervals.of_fin 109 1 valid_sub9_1
lemma valid_sub9_2 : ∀ i : Fin 1, ValidAt (110 + i.val) := by decide +kernel
lemma valid_part9_2 : FiniteIntervals.Covers ValidAt 110 111 :=
  FiniteIntervals.of_fin 110 1 valid_sub9_2
lemma valid_sub9_3 : ∀ i : Fin 1, ValidAt (111 + i.val) := by decide +kernel
lemma valid_part9_3 : FiniteIntervals.Covers ValidAt 111 112 :=
  FiniteIntervals.of_fin 111 1 valid_sub9_3
lemma valid_sub9_4 : ∀ i : Fin 1, ValidAt (112 + i.val) := by decide +kernel
lemma valid_part9_4 : FiniteIntervals.Covers ValidAt 112 113 :=
  FiniteIntervals.of_fin 112 1 valid_sub9_4
lemma valid_sub9_5 : ∀ i : Fin 1, ValidAt (113 + i.val) := by decide +kernel
lemma valid_part9_5 : FiniteIntervals.Covers ValidAt 113 114 :=
  FiniteIntervals.of_fin 113 1 valid_sub9_5
lemma valid_sub9_6 : ∀ i : Fin 1, ValidAt (114 + i.val) := by decide +kernel
lemma valid_part9_6 : FiniteIntervals.Covers ValidAt 114 115 :=
  FiniteIntervals.of_fin 114 1 valid_sub9_6
lemma valid_sub9_7 : ∀ i : Fin 1, ValidAt (115 + i.val) := by decide +kernel
lemma valid_part9_7 : FiniteIntervals.Covers ValidAt 115 116 :=
  FiniteIntervals.of_fin 115 1 valid_sub9_7
lemma valid_sub9_8 : ∀ i : Fin 1, ValidAt (116 + i.val) := by decide +kernel
lemma valid_part9_8 : FiniteIntervals.Covers ValidAt 116 117 :=
  FiniteIntervals.of_fin 116 1 valid_sub9_8
lemma valid_sub9_9 : ∀ i : Fin 1, ValidAt (117 + i.val) := by decide +kernel
lemma valid_part9_9 : FiniteIntervals.Covers ValidAt 117 118 :=
  FiniteIntervals.of_fin 117 1 valid_sub9_9
lemma valid_sub9_10 : ∀ i : Fin 1, ValidAt (118 + i.val) := by decide +kernel
lemma valid_part9_10 : FiniteIntervals.Covers ValidAt 118 119 :=
  FiniteIntervals.of_fin 118 1 valid_sub9_10
lemma valid_sub9_11 : ∀ i : Fin 1, ValidAt (119 + i.val) := by decide +kernel
lemma valid_part9_11 : FiniteIntervals.Covers ValidAt 119 120 :=
  FiniteIntervals.of_fin 119 1 valid_sub9_11
lemma valid_interval9 : FiniteIntervals.Covers ValidAt 108 120 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part9_0 (FiniteIntervals.merge valid_part9_1 valid_part9_2)) (FiniteIntervals.merge valid_part9_3 (FiniteIntervals.merge valid_part9_4 valid_part9_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part9_6 (FiniteIntervals.merge valid_part9_7 valid_part9_8)) (FiniteIntervals.merge valid_part9_9 (FiniteIntervals.merge valid_part9_10 valid_part9_11))))
#print axioms valid_interval9
end Erdos184Work.PureSixActions0
