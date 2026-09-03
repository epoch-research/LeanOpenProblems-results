import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub34_0 : ∀ i : Fin 1, ValidAt (408 + i.val) := by decide +kernel
lemma valid_part34_0 : FiniteIntervals.Covers ValidAt 408 409 :=
  FiniteIntervals.of_fin 408 1 valid_sub34_0
lemma valid_sub34_1 : ∀ i : Fin 1, ValidAt (409 + i.val) := by decide +kernel
lemma valid_part34_1 : FiniteIntervals.Covers ValidAt 409 410 :=
  FiniteIntervals.of_fin 409 1 valid_sub34_1
lemma valid_sub34_2 : ∀ i : Fin 1, ValidAt (410 + i.val) := by decide +kernel
lemma valid_part34_2 : FiniteIntervals.Covers ValidAt 410 411 :=
  FiniteIntervals.of_fin 410 1 valid_sub34_2
lemma valid_sub34_3 : ∀ i : Fin 1, ValidAt (411 + i.val) := by decide +kernel
lemma valid_part34_3 : FiniteIntervals.Covers ValidAt 411 412 :=
  FiniteIntervals.of_fin 411 1 valid_sub34_3
lemma valid_sub34_4 : ∀ i : Fin 1, ValidAt (412 + i.val) := by decide +kernel
lemma valid_part34_4 : FiniteIntervals.Covers ValidAt 412 413 :=
  FiniteIntervals.of_fin 412 1 valid_sub34_4
lemma valid_sub34_5 : ∀ i : Fin 1, ValidAt (413 + i.val) := by decide +kernel
lemma valid_part34_5 : FiniteIntervals.Covers ValidAt 413 414 :=
  FiniteIntervals.of_fin 413 1 valid_sub34_5
lemma valid_sub34_6 : ∀ i : Fin 1, ValidAt (414 + i.val) := by decide +kernel
lemma valid_part34_6 : FiniteIntervals.Covers ValidAt 414 415 :=
  FiniteIntervals.of_fin 414 1 valid_sub34_6
lemma valid_sub34_7 : ∀ i : Fin 1, ValidAt (415 + i.val) := by decide +kernel
lemma valid_part34_7 : FiniteIntervals.Covers ValidAt 415 416 :=
  FiniteIntervals.of_fin 415 1 valid_sub34_7
lemma valid_sub34_8 : ∀ i : Fin 1, ValidAt (416 + i.val) := by decide +kernel
lemma valid_part34_8 : FiniteIntervals.Covers ValidAt 416 417 :=
  FiniteIntervals.of_fin 416 1 valid_sub34_8
lemma valid_sub34_9 : ∀ i : Fin 1, ValidAt (417 + i.val) := by decide +kernel
lemma valid_part34_9 : FiniteIntervals.Covers ValidAt 417 418 :=
  FiniteIntervals.of_fin 417 1 valid_sub34_9
lemma valid_sub34_10 : ∀ i : Fin 1, ValidAt (418 + i.val) := by decide +kernel
lemma valid_part34_10 : FiniteIntervals.Covers ValidAt 418 419 :=
  FiniteIntervals.of_fin 418 1 valid_sub34_10
lemma valid_sub34_11 : ∀ i : Fin 1, ValidAt (419 + i.val) := by decide +kernel
lemma valid_part34_11 : FiniteIntervals.Covers ValidAt 419 420 :=
  FiniteIntervals.of_fin 419 1 valid_sub34_11
lemma valid_interval34 : FiniteIntervals.Covers ValidAt 408 420 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part34_0 (FiniteIntervals.merge valid_part34_1 valid_part34_2)) (FiniteIntervals.merge valid_part34_3 (FiniteIntervals.merge valid_part34_4 valid_part34_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part34_6 (FiniteIntervals.merge valid_part34_7 valid_part34_8)) (FiniteIntervals.merge valid_part34_9 (FiniteIntervals.merge valid_part34_10 valid_part34_11))))
#print axioms valid_interval34
end Erdos184Work.PureSixActions0
