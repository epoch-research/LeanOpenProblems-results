import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub59_0 : ∀ i : Fin 1, ValidAt (708 + i.val) := by decide +kernel
lemma valid_part59_0 : FiniteIntervals.Covers ValidAt 708 709 :=
  FiniteIntervals.of_fin 708 1 valid_sub59_0
lemma valid_sub59_1 : ∀ i : Fin 1, ValidAt (709 + i.val) := by decide +kernel
lemma valid_part59_1 : FiniteIntervals.Covers ValidAt 709 710 :=
  FiniteIntervals.of_fin 709 1 valid_sub59_1
lemma valid_sub59_2 : ∀ i : Fin 1, ValidAt (710 + i.val) := by decide +kernel
lemma valid_part59_2 : FiniteIntervals.Covers ValidAt 710 711 :=
  FiniteIntervals.of_fin 710 1 valid_sub59_2
lemma valid_sub59_3 : ∀ i : Fin 1, ValidAt (711 + i.val) := by decide +kernel
lemma valid_part59_3 : FiniteIntervals.Covers ValidAt 711 712 :=
  FiniteIntervals.of_fin 711 1 valid_sub59_3
lemma valid_sub59_4 : ∀ i : Fin 1, ValidAt (712 + i.val) := by decide +kernel
lemma valid_part59_4 : FiniteIntervals.Covers ValidAt 712 713 :=
  FiniteIntervals.of_fin 712 1 valid_sub59_4
lemma valid_sub59_5 : ∀ i : Fin 1, ValidAt (713 + i.val) := by decide +kernel
lemma valid_part59_5 : FiniteIntervals.Covers ValidAt 713 714 :=
  FiniteIntervals.of_fin 713 1 valid_sub59_5
lemma valid_sub59_6 : ∀ i : Fin 1, ValidAt (714 + i.val) := by decide +kernel
lemma valid_part59_6 : FiniteIntervals.Covers ValidAt 714 715 :=
  FiniteIntervals.of_fin 714 1 valid_sub59_6
lemma valid_sub59_7 : ∀ i : Fin 1, ValidAt (715 + i.val) := by decide +kernel
lemma valid_part59_7 : FiniteIntervals.Covers ValidAt 715 716 :=
  FiniteIntervals.of_fin 715 1 valid_sub59_7
lemma valid_sub59_8 : ∀ i : Fin 1, ValidAt (716 + i.val) := by decide +kernel
lemma valid_part59_8 : FiniteIntervals.Covers ValidAt 716 717 :=
  FiniteIntervals.of_fin 716 1 valid_sub59_8
lemma valid_sub59_9 : ∀ i : Fin 1, ValidAt (717 + i.val) := by decide +kernel
lemma valid_part59_9 : FiniteIntervals.Covers ValidAt 717 718 :=
  FiniteIntervals.of_fin 717 1 valid_sub59_9
lemma valid_sub59_10 : ∀ i : Fin 1, ValidAt (718 + i.val) := by decide +kernel
lemma valid_part59_10 : FiniteIntervals.Covers ValidAt 718 719 :=
  FiniteIntervals.of_fin 718 1 valid_sub59_10
lemma valid_sub59_11 : ∀ i : Fin 1, ValidAt (719 + i.val) := by decide +kernel
lemma valid_part59_11 : FiniteIntervals.Covers ValidAt 719 720 :=
  FiniteIntervals.of_fin 719 1 valid_sub59_11
lemma valid_interval59 : FiniteIntervals.Covers ValidAt 708 720 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part59_0 (FiniteIntervals.merge valid_part59_1 valid_part59_2)) (FiniteIntervals.merge valid_part59_3 (FiniteIntervals.merge valid_part59_4 valid_part59_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part59_6 (FiniteIntervals.merge valid_part59_7 valid_part59_8)) (FiniteIntervals.merge valid_part59_9 (FiniteIntervals.merge valid_part59_10 valid_part59_11))))
#print axioms valid_interval59
end Erdos184Work.PureSixActions0
