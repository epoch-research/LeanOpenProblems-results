import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base8 : BaseValid 8 := by decide +kernel
lemma row8_0 : ∀ q : Fin (choices 0), RowValid 8 0 q := by decide +kernel
lemma row8_1 : ∀ q : Fin (choices 1), RowValid 8 1 q := by decide +kernel
lemma row8_2 : ∀ q : Fin (choices 2), RowValid 8 2 q := by decide +kernel
lemma row8_3 : ∀ q : Fin (choices 3), RowValid 8 3 q := by decide +kernel
lemma row8_4 : ∀ q : Fin (choices 4), RowValid 8 4 q := by decide +kernel
lemma row8_5 : ∀ q : Fin (choices 5), RowValid 8 5 q := by decide +kernel
lemma valid_group8 : Valid 8 := by
  refine ⟨base8.1,base8.2.1,base8.2.2,?_⟩
  intro i
  fin_cases i
  · exact row8_0
  · exact row8_1
  · exact row8_2
  · exact row8_3
  · exact row8_4
  · exact row8_5
lemma valid_sub1_0 : ∀ i : Fin 1, ValidAt (8 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group8
lemma valid_part1_0 : FiniteIntervals.Covers ValidAt 8 9 :=
  FiniteIntervals.of_fin 8 1 valid_sub1_0
lemma base9 : BaseValid 9 := by decide +kernel
lemma row9_0 : ∀ q : Fin (choices 0), RowValid 9 0 q := by decide +kernel
lemma row9_1 : ∀ q : Fin (choices 1), RowValid 9 1 q := by decide +kernel
lemma row9_2 : ∀ q : Fin (choices 2), RowValid 9 2 q := by decide +kernel
lemma row9_3 : ∀ q : Fin (choices 3), RowValid 9 3 q := by decide +kernel
lemma row9_4 : ∀ q : Fin (choices 4), RowValid 9 4 q := by decide +kernel
lemma row9_5 : ∀ q : Fin (choices 5), RowValid 9 5 q := by decide +kernel
lemma valid_group9 : Valid 9 := by
  refine ⟨base9.1,base9.2.1,base9.2.2,?_⟩
  intro i
  fin_cases i
  · exact row9_0
  · exact row9_1
  · exact row9_2
  · exact row9_3
  · exact row9_4
  · exact row9_5
lemma valid_sub1_1 : ∀ i : Fin 1, ValidAt (9 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group9
lemma valid_part1_1 : FiniteIntervals.Covers ValidAt 9 10 :=
  FiniteIntervals.of_fin 9 1 valid_sub1_1
lemma base10 : BaseValid 10 := by decide +kernel
lemma row10_0 : ∀ q : Fin (choices 0), RowValid 10 0 q := by decide +kernel
lemma row10_1 : ∀ q : Fin (choices 1), RowValid 10 1 q := by decide +kernel
lemma row10_2 : ∀ q : Fin (choices 2), RowValid 10 2 q := by decide +kernel
lemma row10_3 : ∀ q : Fin (choices 3), RowValid 10 3 q := by decide +kernel
lemma row10_4 : ∀ q : Fin (choices 4), RowValid 10 4 q := by decide +kernel
lemma row10_5 : ∀ q : Fin (choices 5), RowValid 10 5 q := by decide +kernel
lemma valid_group10 : Valid 10 := by
  refine ⟨base10.1,base10.2.1,base10.2.2,?_⟩
  intro i
  fin_cases i
  · exact row10_0
  · exact row10_1
  · exact row10_2
  · exact row10_3
  · exact row10_4
  · exact row10_5
lemma valid_sub1_2 : ∀ i : Fin 1, ValidAt (10 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group10
lemma valid_part1_2 : FiniteIntervals.Covers ValidAt 10 11 :=
  FiniteIntervals.of_fin 10 1 valid_sub1_2
lemma base11 : BaseValid 11 := by decide +kernel
lemma row11_0 : ∀ q : Fin (choices 0), RowValid 11 0 q := by decide +kernel
lemma row11_1 : ∀ q : Fin (choices 1), RowValid 11 1 q := by decide +kernel
lemma row11_2 : ∀ q : Fin (choices 2), RowValid 11 2 q := by decide +kernel
lemma row11_3 : ∀ q : Fin (choices 3), RowValid 11 3 q := by decide +kernel
lemma row11_4 : ∀ q : Fin (choices 4), RowValid 11 4 q := by decide +kernel
lemma row11_5 : ∀ q : Fin (choices 5), RowValid 11 5 q := by decide +kernel
lemma valid_group11 : Valid 11 := by
  refine ⟨base11.1,base11.2.1,base11.2.2,?_⟩
  intro i
  fin_cases i
  · exact row11_0
  · exact row11_1
  · exact row11_2
  · exact row11_3
  · exact row11_4
  · exact row11_5
lemma valid_sub1_3 : ∀ i : Fin 1, ValidAt (11 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group11
lemma valid_part1_3 : FiniteIntervals.Covers ValidAt 11 12 :=
  FiniteIntervals.of_fin 11 1 valid_sub1_3
lemma base12 : BaseValid 12 := by decide +kernel
lemma row12_0 : ∀ q : Fin (choices 0), RowValid 12 0 q := by decide +kernel
lemma row12_1 : ∀ q : Fin (choices 1), RowValid 12 1 q := by decide +kernel
lemma row12_2 : ∀ q : Fin (choices 2), RowValid 12 2 q := by decide +kernel
lemma row12_3 : ∀ q : Fin (choices 3), RowValid 12 3 q := by decide +kernel
lemma row12_4 : ∀ q : Fin (choices 4), RowValid 12 4 q := by decide +kernel
lemma row12_5 : ∀ q : Fin (choices 5), RowValid 12 5 q := by decide +kernel
lemma valid_group12 : Valid 12 := by
  refine ⟨base12.1,base12.2.1,base12.2.2,?_⟩
  intro i
  fin_cases i
  · exact row12_0
  · exact row12_1
  · exact row12_2
  · exact row12_3
  · exact row12_4
  · exact row12_5
lemma valid_sub1_4 : ∀ i : Fin 1, ValidAt (12 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group12
lemma valid_part1_4 : FiniteIntervals.Covers ValidAt 12 13 :=
  FiniteIntervals.of_fin 12 1 valid_sub1_4
lemma base13 : BaseValid 13 := by decide +kernel
lemma row13_0 : ∀ q : Fin (choices 0), RowValid 13 0 q := by decide +kernel
lemma row13_1 : ∀ q : Fin (choices 1), RowValid 13 1 q := by decide +kernel
lemma row13_2 : ∀ q : Fin (choices 2), RowValid 13 2 q := by decide +kernel
lemma row13_3 : ∀ q : Fin (choices 3), RowValid 13 3 q := by decide +kernel
lemma row13_4 : ∀ q : Fin (choices 4), RowValid 13 4 q := by decide +kernel
lemma row13_5 : ∀ q : Fin (choices 5), RowValid 13 5 q := by decide +kernel
lemma valid_group13 : Valid 13 := by
  refine ⟨base13.1,base13.2.1,base13.2.2,?_⟩
  intro i
  fin_cases i
  · exact row13_0
  · exact row13_1
  · exact row13_2
  · exact row13_3
  · exact row13_4
  · exact row13_5
lemma valid_sub1_5 : ∀ i : Fin 1, ValidAt (13 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group13
lemma valid_part1_5 : FiniteIntervals.Covers ValidAt 13 14 :=
  FiniteIntervals.of_fin 13 1 valid_sub1_5
lemma base14 : BaseValid 14 := by decide +kernel
lemma row14_0 : ∀ q : Fin (choices 0), RowValid 14 0 q := by decide +kernel
lemma row14_1 : ∀ q : Fin (choices 1), RowValid 14 1 q := by decide +kernel
lemma row14_2 : ∀ q : Fin (choices 2), RowValid 14 2 q := by decide +kernel
lemma row14_3 : ∀ q : Fin (choices 3), RowValid 14 3 q := by decide +kernel
lemma row14_4 : ∀ q : Fin (choices 4), RowValid 14 4 q := by decide +kernel
lemma row14_5 : ∀ q : Fin (choices 5), RowValid 14 5 q := by decide +kernel
lemma valid_group14 : Valid 14 := by
  refine ⟨base14.1,base14.2.1,base14.2.2,?_⟩
  intro i
  fin_cases i
  · exact row14_0
  · exact row14_1
  · exact row14_2
  · exact row14_3
  · exact row14_4
  · exact row14_5
lemma valid_sub1_6 : ∀ i : Fin 1, ValidAt (14 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group14
lemma valid_part1_6 : FiniteIntervals.Covers ValidAt 14 15 :=
  FiniteIntervals.of_fin 14 1 valid_sub1_6
lemma base15 : BaseValid 15 := by decide +kernel
lemma row15_0 : ∀ q : Fin (choices 0), RowValid 15 0 q := by decide +kernel
lemma row15_1 : ∀ q : Fin (choices 1), RowValid 15 1 q := by decide +kernel
lemma row15_2 : ∀ q : Fin (choices 2), RowValid 15 2 q := by decide +kernel
lemma row15_3 : ∀ q : Fin (choices 3), RowValid 15 3 q := by decide +kernel
lemma row15_4 : ∀ q : Fin (choices 4), RowValid 15 4 q := by decide +kernel
lemma row15_5 : ∀ q : Fin (choices 5), RowValid 15 5 q := by decide +kernel
lemma valid_group15 : Valid 15 := by
  refine ⟨base15.1,base15.2.1,base15.2.2,?_⟩
  intro i
  fin_cases i
  · exact row15_0
  · exact row15_1
  · exact row15_2
  · exact row15_3
  · exact row15_4
  · exact row15_5
lemma valid_sub1_7 : ∀ i : Fin 1, ValidAt (15 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group15
lemma valid_part1_7 : FiniteIntervals.Covers ValidAt 15 16 :=
  FiniteIntervals.of_fin 15 1 valid_sub1_7
lemma valid_interval1 : FiniteIntervals.Covers ValidAt 8 16 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part1_0 valid_part1_1) (FiniteIntervals.merge valid_part1_2 valid_part1_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part1_4 valid_part1_5) (FiniteIntervals.merge valid_part1_6 valid_part1_7)))
#print axioms valid_interval1
end Erdos184Work.PureSixActions2
