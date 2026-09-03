import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub20_0 : ∀ i : Fin 1, ValidAt (240 + i.val) := by decide +kernel
lemma valid_part20_0 : FiniteIntervals.Covers ValidAt 240 241 :=
  FiniteIntervals.of_fin 240 1 valid_sub20_0
lemma valid_sub20_1 : ∀ i : Fin 1, ValidAt (241 + i.val) := by decide +kernel
lemma valid_part20_1 : FiniteIntervals.Covers ValidAt 241 242 :=
  FiniteIntervals.of_fin 241 1 valid_sub20_1
lemma valid_sub20_2 : ∀ i : Fin 1, ValidAt (242 + i.val) := by decide +kernel
lemma valid_part20_2 : FiniteIntervals.Covers ValidAt 242 243 :=
  FiniteIntervals.of_fin 242 1 valid_sub20_2
lemma valid_sub20_3 : ∀ i : Fin 1, ValidAt (243 + i.val) := by decide +kernel
lemma valid_part20_3 : FiniteIntervals.Covers ValidAt 243 244 :=
  FiniteIntervals.of_fin 243 1 valid_sub20_3
lemma valid_sub20_4 : ∀ i : Fin 1, ValidAt (244 + i.val) := by decide +kernel
lemma valid_part20_4 : FiniteIntervals.Covers ValidAt 244 245 :=
  FiniteIntervals.of_fin 244 1 valid_sub20_4
lemma valid_sub20_5 : ∀ i : Fin 1, ValidAt (245 + i.val) := by decide +kernel
lemma valid_part20_5 : FiniteIntervals.Covers ValidAt 245 246 :=
  FiniteIntervals.of_fin 245 1 valid_sub20_5
lemma valid_sub20_6 : ∀ i : Fin 1, ValidAt (246 + i.val) := by decide +kernel
lemma valid_part20_6 : FiniteIntervals.Covers ValidAt 246 247 :=
  FiniteIntervals.of_fin 246 1 valid_sub20_6
lemma valid_sub20_7 : ∀ i : Fin 1, ValidAt (247 + i.val) := by decide +kernel
lemma valid_part20_7 : FiniteIntervals.Covers ValidAt 247 248 :=
  FiniteIntervals.of_fin 247 1 valid_sub20_7
lemma valid_sub20_8 : ∀ i : Fin 1, ValidAt (248 + i.val) := by decide +kernel
lemma valid_part20_8 : FiniteIntervals.Covers ValidAt 248 249 :=
  FiniteIntervals.of_fin 248 1 valid_sub20_8
lemma valid_sub20_9 : ∀ i : Fin 1, ValidAt (249 + i.val) := by decide +kernel
lemma valid_part20_9 : FiniteIntervals.Covers ValidAt 249 250 :=
  FiniteIntervals.of_fin 249 1 valid_sub20_9
lemma valid_sub20_10 : ∀ i : Fin 1, ValidAt (250 + i.val) := by decide +kernel
lemma valid_part20_10 : FiniteIntervals.Covers ValidAt 250 251 :=
  FiniteIntervals.of_fin 250 1 valid_sub20_10
lemma valid_sub20_11 : ∀ i : Fin 1, ValidAt (251 + i.val) := by decide +kernel
lemma valid_part20_11 : FiniteIntervals.Covers ValidAt 251 252 :=
  FiniteIntervals.of_fin 251 1 valid_sub20_11
lemma valid_interval20 : FiniteIntervals.Covers ValidAt 240 252 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part20_0 (FiniteIntervals.merge valid_part20_1 valid_part20_2)) (FiniteIntervals.merge valid_part20_3 (FiniteIntervals.merge valid_part20_4 valid_part20_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part20_6 (FiniteIntervals.merge valid_part20_7 valid_part20_8)) (FiniteIntervals.merge valid_part20_9 (FiniteIntervals.merge valid_part20_10 valid_part20_11))))
#print axioms valid_interval20
end Erdos184Work.PureSixActions0
