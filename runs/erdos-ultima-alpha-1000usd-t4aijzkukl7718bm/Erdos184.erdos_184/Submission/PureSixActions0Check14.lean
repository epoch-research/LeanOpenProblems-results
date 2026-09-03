import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub14_0 : ∀ i : Fin 1, ValidAt (168 + i.val) := by decide +kernel
lemma valid_part14_0 : FiniteIntervals.Covers ValidAt 168 169 :=
  FiniteIntervals.of_fin 168 1 valid_sub14_0
lemma valid_sub14_1 : ∀ i : Fin 1, ValidAt (169 + i.val) := by decide +kernel
lemma valid_part14_1 : FiniteIntervals.Covers ValidAt 169 170 :=
  FiniteIntervals.of_fin 169 1 valid_sub14_1
lemma valid_sub14_2 : ∀ i : Fin 1, ValidAt (170 + i.val) := by decide +kernel
lemma valid_part14_2 : FiniteIntervals.Covers ValidAt 170 171 :=
  FiniteIntervals.of_fin 170 1 valid_sub14_2
lemma valid_sub14_3 : ∀ i : Fin 1, ValidAt (171 + i.val) := by decide +kernel
lemma valid_part14_3 : FiniteIntervals.Covers ValidAt 171 172 :=
  FiniteIntervals.of_fin 171 1 valid_sub14_3
lemma valid_sub14_4 : ∀ i : Fin 1, ValidAt (172 + i.val) := by decide +kernel
lemma valid_part14_4 : FiniteIntervals.Covers ValidAt 172 173 :=
  FiniteIntervals.of_fin 172 1 valid_sub14_4
lemma valid_sub14_5 : ∀ i : Fin 1, ValidAt (173 + i.val) := by decide +kernel
lemma valid_part14_5 : FiniteIntervals.Covers ValidAt 173 174 :=
  FiniteIntervals.of_fin 173 1 valid_sub14_5
lemma valid_sub14_6 : ∀ i : Fin 1, ValidAt (174 + i.val) := by decide +kernel
lemma valid_part14_6 : FiniteIntervals.Covers ValidAt 174 175 :=
  FiniteIntervals.of_fin 174 1 valid_sub14_6
lemma valid_sub14_7 : ∀ i : Fin 1, ValidAt (175 + i.val) := by decide +kernel
lemma valid_part14_7 : FiniteIntervals.Covers ValidAt 175 176 :=
  FiniteIntervals.of_fin 175 1 valid_sub14_7
lemma valid_sub14_8 : ∀ i : Fin 1, ValidAt (176 + i.val) := by decide +kernel
lemma valid_part14_8 : FiniteIntervals.Covers ValidAt 176 177 :=
  FiniteIntervals.of_fin 176 1 valid_sub14_8
lemma valid_sub14_9 : ∀ i : Fin 1, ValidAt (177 + i.val) := by decide +kernel
lemma valid_part14_9 : FiniteIntervals.Covers ValidAt 177 178 :=
  FiniteIntervals.of_fin 177 1 valid_sub14_9
lemma valid_sub14_10 : ∀ i : Fin 1, ValidAt (178 + i.val) := by decide +kernel
lemma valid_part14_10 : FiniteIntervals.Covers ValidAt 178 179 :=
  FiniteIntervals.of_fin 178 1 valid_sub14_10
lemma valid_sub14_11 : ∀ i : Fin 1, ValidAt (179 + i.val) := by decide +kernel
lemma valid_part14_11 : FiniteIntervals.Covers ValidAt 179 180 :=
  FiniteIntervals.of_fin 179 1 valid_sub14_11
lemma valid_interval14 : FiniteIntervals.Covers ValidAt 168 180 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part14_0 (FiniteIntervals.merge valid_part14_1 valid_part14_2)) (FiniteIntervals.merge valid_part14_3 (FiniteIntervals.merge valid_part14_4 valid_part14_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part14_6 (FiniteIntervals.merge valid_part14_7 valid_part14_8)) (FiniteIntervals.merge valid_part14_9 (FiniteIntervals.merge valid_part14_10 valid_part14_11))))
#print axioms valid_interval14
end Erdos184Work.PureSixActions0
