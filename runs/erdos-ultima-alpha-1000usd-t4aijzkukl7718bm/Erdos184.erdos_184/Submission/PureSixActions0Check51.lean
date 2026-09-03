import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_sub51_0 : ∀ i : Fin 1, ValidAt (612 + i.val) := by decide +kernel
lemma valid_part51_0 : FiniteIntervals.Covers ValidAt 612 613 :=
  FiniteIntervals.of_fin 612 1 valid_sub51_0
lemma valid_sub51_1 : ∀ i : Fin 1, ValidAt (613 + i.val) := by decide +kernel
lemma valid_part51_1 : FiniteIntervals.Covers ValidAt 613 614 :=
  FiniteIntervals.of_fin 613 1 valid_sub51_1
lemma valid_sub51_2 : ∀ i : Fin 1, ValidAt (614 + i.val) := by decide +kernel
lemma valid_part51_2 : FiniteIntervals.Covers ValidAt 614 615 :=
  FiniteIntervals.of_fin 614 1 valid_sub51_2
lemma valid_sub51_3 : ∀ i : Fin 1, ValidAt (615 + i.val) := by decide +kernel
lemma valid_part51_3 : FiniteIntervals.Covers ValidAt 615 616 :=
  FiniteIntervals.of_fin 615 1 valid_sub51_3
lemma valid_sub51_4 : ∀ i : Fin 1, ValidAt (616 + i.val) := by decide +kernel
lemma valid_part51_4 : FiniteIntervals.Covers ValidAt 616 617 :=
  FiniteIntervals.of_fin 616 1 valid_sub51_4
lemma valid_sub51_5 : ∀ i : Fin 1, ValidAt (617 + i.val) := by decide +kernel
lemma valid_part51_5 : FiniteIntervals.Covers ValidAt 617 618 :=
  FiniteIntervals.of_fin 617 1 valid_sub51_5
lemma valid_sub51_6 : ∀ i : Fin 1, ValidAt (618 + i.val) := by decide +kernel
lemma valid_part51_6 : FiniteIntervals.Covers ValidAt 618 619 :=
  FiniteIntervals.of_fin 618 1 valid_sub51_6
lemma valid_sub51_7 : ∀ i : Fin 1, ValidAt (619 + i.val) := by decide +kernel
lemma valid_part51_7 : FiniteIntervals.Covers ValidAt 619 620 :=
  FiniteIntervals.of_fin 619 1 valid_sub51_7
lemma valid_sub51_8 : ∀ i : Fin 1, ValidAt (620 + i.val) := by decide +kernel
lemma valid_part51_8 : FiniteIntervals.Covers ValidAt 620 621 :=
  FiniteIntervals.of_fin 620 1 valid_sub51_8
lemma valid_sub51_9 : ∀ i : Fin 1, ValidAt (621 + i.val) := by decide +kernel
lemma valid_part51_9 : FiniteIntervals.Covers ValidAt 621 622 :=
  FiniteIntervals.of_fin 621 1 valid_sub51_9
lemma valid_sub51_10 : ∀ i : Fin 1, ValidAt (622 + i.val) := by decide +kernel
lemma valid_part51_10 : FiniteIntervals.Covers ValidAt 622 623 :=
  FiniteIntervals.of_fin 622 1 valid_sub51_10
lemma valid_sub51_11 : ∀ i : Fin 1, ValidAt (623 + i.val) := by decide +kernel
lemma valid_part51_11 : FiniteIntervals.Covers ValidAt 623 624 :=
  FiniteIntervals.of_fin 623 1 valid_sub51_11
lemma valid_interval51 : FiniteIntervals.Covers ValidAt 612 624 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part51_0 (FiniteIntervals.merge valid_part51_1 valid_part51_2)) (FiniteIntervals.merge valid_part51_3 (FiniteIntervals.merge valid_part51_4 valid_part51_5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_part51_6 (FiniteIntervals.merge valid_part51_7 valid_part51_8)) (FiniteIntervals.merge valid_part51_9 (FiniteIntervals.merge valid_part51_10 valid_part51_11))))
#print axioms valid_interval51
end Erdos184Work.PureSixActions0
