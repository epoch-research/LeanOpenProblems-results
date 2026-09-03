import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub55_0 : ∀ i : Fin 1, ValidAt (660 + i.val) := by decide +kernel
lemma valid_part55_0 : FiniteIntervals.Covers ValidAt 660 661 :=
  FiniteIntervals.of_fin 660 1 valid_sub55_0
lemma valid_sub55_1 : ∀ i : Fin 1, ValidAt (661 + i.val) := by decide +kernel
lemma valid_part55_1 : FiniteIntervals.Covers ValidAt 661 662 :=
  FiniteIntervals.of_fin 661 1 valid_sub55_1
lemma valid_sub55_2 : ∀ i : Fin 1, ValidAt (662 + i.val) := by decide +kernel
lemma valid_part55_2 : FiniteIntervals.Covers ValidAt 662 663 :=
  FiniteIntervals.of_fin 662 1 valid_sub55_2
lemma valid_sub55_3 : ∀ i : Fin 1, ValidAt (663 + i.val) := by decide +kernel
lemma valid_part55_3 : FiniteIntervals.Covers ValidAt 663 664 :=
  FiniteIntervals.of_fin 663 1 valid_sub55_3
lemma valid_sub55_4 : ∀ i : Fin 1, ValidAt (664 + i.val) := by decide +kernel
lemma valid_part55_4 : FiniteIntervals.Covers ValidAt 664 665 :=
  FiniteIntervals.of_fin 664 1 valid_sub55_4
lemma valid_sub55_5 : ∀ i : Fin 1, ValidAt (665 + i.val) := by decide +kernel
lemma valid_part55_5 : FiniteIntervals.Covers ValidAt 665 666 :=
  FiniteIntervals.of_fin 665 1 valid_sub55_5
lemma valid_sub55_6 : ∀ i : Fin 1, ValidAt (666 + i.val) := by decide +kernel
lemma valid_part55_6 : FiniteIntervals.Covers ValidAt 666 667 :=
  FiniteIntervals.of_fin 666 1 valid_sub55_6
lemma valid_sub55_7 : ∀ i : Fin 1, ValidAt (667 + i.val) := by decide +kernel
lemma valid_part55_7 : FiniteIntervals.Covers ValidAt 667 668 :=
  FiniteIntervals.of_fin 667 1 valid_sub55_7
lemma valid_sub55_8 : ∀ i : Fin 1, ValidAt (668 + i.val) := by decide +kernel
lemma valid_part55_8 : FiniteIntervals.Covers ValidAt 668 669 :=
  FiniteIntervals.of_fin 668 1 valid_sub55_8
lemma valid_sub55_9 : ∀ i : Fin 1, ValidAt (669 + i.val) := by decide +kernel
lemma valid_part55_9 : FiniteIntervals.Covers ValidAt 669 670 :=
  FiniteIntervals.of_fin 669 1 valid_sub55_9
lemma valid_sub55_10 : ∀ i : Fin 1, ValidAt (670 + i.val) := by decide +kernel
lemma valid_part55_10 : FiniteIntervals.Covers ValidAt 670 671 :=
  FiniteIntervals.of_fin 670 1 valid_sub55_10
lemma valid_sub55_11 : ∀ i : Fin 1, ValidAt (671 + i.val) := by decide +kernel
lemma valid_part55_11 : FiniteIntervals.Covers ValidAt 671 672 :=
  FiniteIntervals.of_fin 671 1 valid_sub55_11
lemma valid_interval55 : FiniteIntervals.Covers ValidAt 660 672 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part55_0 (FiniteIntervals.merge valid_part55_1 valid_part55_2)) (FiniteIntervals.merge valid_part55_3 (FiniteIntervals.merge valid_part55_4 valid_part55_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part55_6 (FiniteIntervals.merge valid_part55_7 valid_part55_8)) (FiniteIntervals.merge valid_part55_9 (FiniteIntervals.merge valid_part55_10 valid_part55_11))))
#print axioms valid_interval55
end Erdos184Work.PureSixActions0
