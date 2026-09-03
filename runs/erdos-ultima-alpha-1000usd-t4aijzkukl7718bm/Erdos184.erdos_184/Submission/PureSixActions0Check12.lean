import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub12_0 : ∀ i : Fin 1, ValidAt (144 + i.val) := by decide +kernel
lemma valid_part12_0 : FiniteIntervals.Covers ValidAt 144 145 :=
  FiniteIntervals.of_fin 144 1 valid_sub12_0
lemma valid_sub12_1 : ∀ i : Fin 1, ValidAt (145 + i.val) := by decide +kernel
lemma valid_part12_1 : FiniteIntervals.Covers ValidAt 145 146 :=
  FiniteIntervals.of_fin 145 1 valid_sub12_1
lemma valid_sub12_2 : ∀ i : Fin 1, ValidAt (146 + i.val) := by decide +kernel
lemma valid_part12_2 : FiniteIntervals.Covers ValidAt 146 147 :=
  FiniteIntervals.of_fin 146 1 valid_sub12_2
lemma valid_sub12_3 : ∀ i : Fin 1, ValidAt (147 + i.val) := by decide +kernel
lemma valid_part12_3 : FiniteIntervals.Covers ValidAt 147 148 :=
  FiniteIntervals.of_fin 147 1 valid_sub12_3
lemma valid_sub12_4 : ∀ i : Fin 1, ValidAt (148 + i.val) := by decide +kernel
lemma valid_part12_4 : FiniteIntervals.Covers ValidAt 148 149 :=
  FiniteIntervals.of_fin 148 1 valid_sub12_4
lemma valid_sub12_5 : ∀ i : Fin 1, ValidAt (149 + i.val) := by decide +kernel
lemma valid_part12_5 : FiniteIntervals.Covers ValidAt 149 150 :=
  FiniteIntervals.of_fin 149 1 valid_sub12_5
lemma valid_sub12_6 : ∀ i : Fin 1, ValidAt (150 + i.val) := by decide +kernel
lemma valid_part12_6 : FiniteIntervals.Covers ValidAt 150 151 :=
  FiniteIntervals.of_fin 150 1 valid_sub12_6
lemma valid_sub12_7 : ∀ i : Fin 1, ValidAt (151 + i.val) := by decide +kernel
lemma valid_part12_7 : FiniteIntervals.Covers ValidAt 151 152 :=
  FiniteIntervals.of_fin 151 1 valid_sub12_7
lemma valid_sub12_8 : ∀ i : Fin 1, ValidAt (152 + i.val) := by decide +kernel
lemma valid_part12_8 : FiniteIntervals.Covers ValidAt 152 153 :=
  FiniteIntervals.of_fin 152 1 valid_sub12_8
lemma valid_sub12_9 : ∀ i : Fin 1, ValidAt (153 + i.val) := by decide +kernel
lemma valid_part12_9 : FiniteIntervals.Covers ValidAt 153 154 :=
  FiniteIntervals.of_fin 153 1 valid_sub12_9
lemma valid_sub12_10 : ∀ i : Fin 1, ValidAt (154 + i.val) := by decide +kernel
lemma valid_part12_10 : FiniteIntervals.Covers ValidAt 154 155 :=
  FiniteIntervals.of_fin 154 1 valid_sub12_10
lemma valid_sub12_11 : ∀ i : Fin 1, ValidAt (155 + i.val) := by decide +kernel
lemma valid_part12_11 : FiniteIntervals.Covers ValidAt 155 156 :=
  FiniteIntervals.of_fin 155 1 valid_sub12_11
lemma valid_interval12 : FiniteIntervals.Covers ValidAt 144 156 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part12_0 (FiniteIntervals.merge valid_part12_1 valid_part12_2)) (FiniteIntervals.merge valid_part12_3 (FiniteIntervals.merge valid_part12_4 valid_part12_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part12_6 (FiniteIntervals.merge valid_part12_7 valid_part12_8)) (FiniteIntervals.merge valid_part12_9 (FiniteIntervals.merge valid_part12_10 valid_part12_11))))
#print axioms valid_interval12
end Erdos184Work.PureSixActions0
