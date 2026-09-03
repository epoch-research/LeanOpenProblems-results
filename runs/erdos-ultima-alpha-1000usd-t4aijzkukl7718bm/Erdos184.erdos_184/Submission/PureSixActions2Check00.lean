import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base0 : BaseValid 0 := by decide +kernel
lemma row0_0 : ∀ q : Fin (choices 0), RowValid 0 0 q := by decide +kernel
lemma row0_1 : ∀ q : Fin (choices 1), RowValid 0 1 q := by decide +kernel
lemma row0_2 : ∀ q : Fin (choices 2), RowValid 0 2 q := by decide +kernel
lemma row0_3 : ∀ q : Fin (choices 3), RowValid 0 3 q := by decide +kernel
lemma row0_4 : ∀ q : Fin (choices 4), RowValid 0 4 q := by decide +kernel
lemma row0_5 : ∀ q : Fin (choices 5), RowValid 0 5 q := by decide +kernel
lemma valid_group0 : Valid 0 := by
  refine ⟨base0.1,base0.2.1,base0.2.2,?_⟩
  intro i
  fin_cases i
  · exact row0_0
  · exact row0_1
  · exact row0_2
  · exact row0_3
  · exact row0_4
  · exact row0_5
lemma valid_sub0_0 : ∀ i : Fin 1, ValidAt (0 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group0
lemma valid_part0_0 : FiniteIntervals.Covers ValidAt 0 1 :=
  FiniteIntervals.of_fin 0 1 valid_sub0_0
lemma base1 : BaseValid 1 := by decide +kernel
lemma row1_0 : ∀ q : Fin (choices 0), RowValid 1 0 q := by decide +kernel
lemma row1_1 : ∀ q : Fin (choices 1), RowValid 1 1 q := by decide +kernel
lemma row1_2 : ∀ q : Fin (choices 2), RowValid 1 2 q := by decide +kernel
lemma row1_3 : ∀ q : Fin (choices 3), RowValid 1 3 q := by decide +kernel
lemma row1_4 : ∀ q : Fin (choices 4), RowValid 1 4 q := by decide +kernel
lemma row1_5 : ∀ q : Fin (choices 5), RowValid 1 5 q := by decide +kernel
lemma valid_group1 : Valid 1 := by
  refine ⟨base1.1,base1.2.1,base1.2.2,?_⟩
  intro i
  fin_cases i
  · exact row1_0
  · exact row1_1
  · exact row1_2
  · exact row1_3
  · exact row1_4
  · exact row1_5
lemma valid_sub0_1 : ∀ i : Fin 1, ValidAt (1 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group1
lemma valid_part0_1 : FiniteIntervals.Covers ValidAt 1 2 :=
  FiniteIntervals.of_fin 1 1 valid_sub0_1
lemma base2 : BaseValid 2 := by decide +kernel
lemma row2_0 : ∀ q : Fin (choices 0), RowValid 2 0 q := by decide +kernel
lemma row2_1 : ∀ q : Fin (choices 1), RowValid 2 1 q := by decide +kernel
lemma row2_2 : ∀ q : Fin (choices 2), RowValid 2 2 q := by decide +kernel
lemma row2_3 : ∀ q : Fin (choices 3), RowValid 2 3 q := by decide +kernel
lemma row2_4 : ∀ q : Fin (choices 4), RowValid 2 4 q := by decide +kernel
lemma row2_5 : ∀ q : Fin (choices 5), RowValid 2 5 q := by decide +kernel
lemma valid_group2 : Valid 2 := by
  refine ⟨base2.1,base2.2.1,base2.2.2,?_⟩
  intro i
  fin_cases i
  · exact row2_0
  · exact row2_1
  · exact row2_2
  · exact row2_3
  · exact row2_4
  · exact row2_5
lemma valid_sub0_2 : ∀ i : Fin 1, ValidAt (2 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group2
lemma valid_part0_2 : FiniteIntervals.Covers ValidAt 2 3 :=
  FiniteIntervals.of_fin 2 1 valid_sub0_2
lemma base3 : BaseValid 3 := by decide +kernel
lemma row3_0 : ∀ q : Fin (choices 0), RowValid 3 0 q := by decide +kernel
lemma row3_1 : ∀ q : Fin (choices 1), RowValid 3 1 q := by decide +kernel
lemma row3_2 : ∀ q : Fin (choices 2), RowValid 3 2 q := by decide +kernel
lemma row3_3 : ∀ q : Fin (choices 3), RowValid 3 3 q := by decide +kernel
lemma row3_4 : ∀ q : Fin (choices 4), RowValid 3 4 q := by decide +kernel
lemma row3_5 : ∀ q : Fin (choices 5), RowValid 3 5 q := by decide +kernel
lemma valid_group3 : Valid 3 := by
  refine ⟨base3.1,base3.2.1,base3.2.2,?_⟩
  intro i
  fin_cases i
  · exact row3_0
  · exact row3_1
  · exact row3_2
  · exact row3_3
  · exact row3_4
  · exact row3_5
lemma valid_sub0_3 : ∀ i : Fin 1, ValidAt (3 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group3
lemma valid_part0_3 : FiniteIntervals.Covers ValidAt 3 4 :=
  FiniteIntervals.of_fin 3 1 valid_sub0_3
lemma base4 : BaseValid 4 := by decide +kernel
lemma row4_0 : ∀ q : Fin (choices 0), RowValid 4 0 q := by decide +kernel
lemma row4_1 : ∀ q : Fin (choices 1), RowValid 4 1 q := by decide +kernel
lemma row4_2 : ∀ q : Fin (choices 2), RowValid 4 2 q := by decide +kernel
lemma row4_3 : ∀ q : Fin (choices 3), RowValid 4 3 q := by decide +kernel
lemma row4_4 : ∀ q : Fin (choices 4), RowValid 4 4 q := by decide +kernel
lemma row4_5 : ∀ q : Fin (choices 5), RowValid 4 5 q := by decide +kernel
lemma valid_group4 : Valid 4 := by
  refine ⟨base4.1,base4.2.1,base4.2.2,?_⟩
  intro i
  fin_cases i
  · exact row4_0
  · exact row4_1
  · exact row4_2
  · exact row4_3
  · exact row4_4
  · exact row4_5
lemma valid_sub0_4 : ∀ i : Fin 1, ValidAt (4 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group4
lemma valid_part0_4 : FiniteIntervals.Covers ValidAt 4 5 :=
  FiniteIntervals.of_fin 4 1 valid_sub0_4
lemma base5 : BaseValid 5 := by decide +kernel
lemma row5_0 : ∀ q : Fin (choices 0), RowValid 5 0 q := by decide +kernel
lemma row5_1 : ∀ q : Fin (choices 1), RowValid 5 1 q := by decide +kernel
lemma row5_2 : ∀ q : Fin (choices 2), RowValid 5 2 q := by decide +kernel
lemma row5_3 : ∀ q : Fin (choices 3), RowValid 5 3 q := by decide +kernel
lemma row5_4 : ∀ q : Fin (choices 4), RowValid 5 4 q := by decide +kernel
lemma row5_5 : ∀ q : Fin (choices 5), RowValid 5 5 q := by decide +kernel
lemma valid_group5 : Valid 5 := by
  refine ⟨base5.1,base5.2.1,base5.2.2,?_⟩
  intro i
  fin_cases i
  · exact row5_0
  · exact row5_1
  · exact row5_2
  · exact row5_3
  · exact row5_4
  · exact row5_5
lemma valid_sub0_5 : ∀ i : Fin 1, ValidAt (5 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group5
lemma valid_part0_5 : FiniteIntervals.Covers ValidAt 5 6 :=
  FiniteIntervals.of_fin 5 1 valid_sub0_5
lemma base6 : BaseValid 6 := by decide +kernel
lemma row6_0 : ∀ q : Fin (choices 0), RowValid 6 0 q := by decide +kernel
lemma row6_1 : ∀ q : Fin (choices 1), RowValid 6 1 q := by decide +kernel
lemma row6_2 : ∀ q : Fin (choices 2), RowValid 6 2 q := by decide +kernel
lemma row6_3 : ∀ q : Fin (choices 3), RowValid 6 3 q := by decide +kernel
lemma row6_4 : ∀ q : Fin (choices 4), RowValid 6 4 q := by decide +kernel
lemma row6_5 : ∀ q : Fin (choices 5), RowValid 6 5 q := by decide +kernel
lemma valid_group6 : Valid 6 := by
  refine ⟨base6.1,base6.2.1,base6.2.2,?_⟩
  intro i
  fin_cases i
  · exact row6_0
  · exact row6_1
  · exact row6_2
  · exact row6_3
  · exact row6_4
  · exact row6_5
lemma valid_sub0_6 : ∀ i : Fin 1, ValidAt (6 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group6
lemma valid_part0_6 : FiniteIntervals.Covers ValidAt 6 7 :=
  FiniteIntervals.of_fin 6 1 valid_sub0_6
lemma base7 : BaseValid 7 := by decide +kernel
lemma row7_0 : ∀ q : Fin (choices 0), RowValid 7 0 q := by decide +kernel
lemma row7_1 : ∀ q : Fin (choices 1), RowValid 7 1 q := by decide +kernel
lemma row7_2 : ∀ q : Fin (choices 2), RowValid 7 2 q := by decide +kernel
lemma row7_3 : ∀ q : Fin (choices 3), RowValid 7 3 q := by decide +kernel
lemma row7_4 : ∀ q : Fin (choices 4), RowValid 7 4 q := by decide +kernel
lemma row7_5 : ∀ q : Fin (choices 5), RowValid 7 5 q := by decide +kernel
lemma valid_group7 : Valid 7 := by
  refine ⟨base7.1,base7.2.1,base7.2.2,?_⟩
  intro i
  fin_cases i
  · exact row7_0
  · exact row7_1
  · exact row7_2
  · exact row7_3
  · exact row7_4
  · exact row7_5
lemma valid_sub0_7 : ∀ i : Fin 1, ValidAt (7 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group7
lemma valid_part0_7 : FiniteIntervals.Covers ValidAt 7 8 :=
  FiniteIntervals.of_fin 7 1 valid_sub0_7
lemma valid_interval0 : FiniteIntervals.Covers ValidAt 0 8 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part0_0 valid_part0_1) (FiniteIntervals.merge valid_part0_2 valid_part0_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part0_4 valid_part0_5) (FiniteIntervals.merge valid_part0_6 valid_part0_7)))
#print axioms valid_interval0
end Erdos184Work.PureSixActions2
