import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub42_0 : ∀ i : Fin 1, ValidAt (504 + i.val) := by decide +kernel
lemma valid_part42_0 : FiniteIntervals.Covers ValidAt 504 505 :=
  FiniteIntervals.of_fin 504 1 valid_sub42_0
lemma valid_sub42_1 : ∀ i : Fin 1, ValidAt (505 + i.val) := by decide +kernel
lemma valid_part42_1 : FiniteIntervals.Covers ValidAt 505 506 :=
  FiniteIntervals.of_fin 505 1 valid_sub42_1
lemma valid_sub42_2 : ∀ i : Fin 1, ValidAt (506 + i.val) := by decide +kernel
lemma valid_part42_2 : FiniteIntervals.Covers ValidAt 506 507 :=
  FiniteIntervals.of_fin 506 1 valid_sub42_2
lemma valid_sub42_3 : ∀ i : Fin 1, ValidAt (507 + i.val) := by decide +kernel
lemma valid_part42_3 : FiniteIntervals.Covers ValidAt 507 508 :=
  FiniteIntervals.of_fin 507 1 valid_sub42_3
lemma valid_sub42_4 : ∀ i : Fin 1, ValidAt (508 + i.val) := by decide +kernel
lemma valid_part42_4 : FiniteIntervals.Covers ValidAt 508 509 :=
  FiniteIntervals.of_fin 508 1 valid_sub42_4
lemma valid_sub42_5 : ∀ i : Fin 1, ValidAt (509 + i.val) := by decide +kernel
lemma valid_part42_5 : FiniteIntervals.Covers ValidAt 509 510 :=
  FiniteIntervals.of_fin 509 1 valid_sub42_5
lemma valid_sub42_6 : ∀ i : Fin 1, ValidAt (510 + i.val) := by decide +kernel
lemma valid_part42_6 : FiniteIntervals.Covers ValidAt 510 511 :=
  FiniteIntervals.of_fin 510 1 valid_sub42_6
lemma valid_sub42_7 : ∀ i : Fin 1, ValidAt (511 + i.val) := by decide +kernel
lemma valid_part42_7 : FiniteIntervals.Covers ValidAt 511 512 :=
  FiniteIntervals.of_fin 511 1 valid_sub42_7
lemma valid_sub42_8 : ∀ i : Fin 1, ValidAt (512 + i.val) := by decide +kernel
lemma valid_part42_8 : FiniteIntervals.Covers ValidAt 512 513 :=
  FiniteIntervals.of_fin 512 1 valid_sub42_8
lemma valid_sub42_9 : ∀ i : Fin 1, ValidAt (513 + i.val) := by decide +kernel
lemma valid_part42_9 : FiniteIntervals.Covers ValidAt 513 514 :=
  FiniteIntervals.of_fin 513 1 valid_sub42_9
lemma valid_sub42_10 : ∀ i : Fin 1, ValidAt (514 + i.val) := by decide +kernel
lemma valid_part42_10 : FiniteIntervals.Covers ValidAt 514 515 :=
  FiniteIntervals.of_fin 514 1 valid_sub42_10
lemma valid_sub42_11 : ∀ i : Fin 1, ValidAt (515 + i.val) := by decide +kernel
lemma valid_part42_11 : FiniteIntervals.Covers ValidAt 515 516 :=
  FiniteIntervals.of_fin 515 1 valid_sub42_11
lemma valid_interval42 : FiniteIntervals.Covers ValidAt 504 516 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part42_0 (FiniteIntervals.merge valid_part42_1 valid_part42_2)) (FiniteIntervals.merge valid_part42_3 (FiniteIntervals.merge valid_part42_4 valid_part42_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part42_6 (FiniteIntervals.merge valid_part42_7 valid_part42_8)) (FiniteIntervals.merge valid_part42_9 (FiniteIntervals.merge valid_part42_10 valid_part42_11))))
#print axioms valid_interval42
end Erdos184Work.PureSixActions0
