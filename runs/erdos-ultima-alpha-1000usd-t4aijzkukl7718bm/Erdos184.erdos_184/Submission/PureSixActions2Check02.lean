import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base16 : BaseValid 16 := by decide +kernel
lemma row16_0 : ∀ q : Fin (choices 0), RowValid 16 0 q := by decide +kernel
lemma row16_1 : ∀ q : Fin (choices 1), RowValid 16 1 q := by decide +kernel
lemma row16_2 : ∀ q : Fin (choices 2), RowValid 16 2 q := by decide +kernel
lemma row16_3 : ∀ q : Fin (choices 3), RowValid 16 3 q := by decide +kernel
lemma row16_4 : ∀ q : Fin (choices 4), RowValid 16 4 q := by decide +kernel
lemma row16_5 : ∀ q : Fin (choices 5), RowValid 16 5 q := by decide +kernel
lemma valid_group16 : Valid 16 := by
  refine ⟨base16.1,base16.2.1,base16.2.2,?_⟩
  intro i
  fin_cases i
  · exact row16_0
  · exact row16_1
  · exact row16_2
  · exact row16_3
  · exact row16_4
  · exact row16_5
lemma valid_sub2_0 : ∀ i : Fin 1, ValidAt (16 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group16
lemma valid_part2_0 : FiniteIntervals.Covers ValidAt 16 17 :=
  FiniteIntervals.of_fin 16 1 valid_sub2_0
lemma base17 : BaseValid 17 := by decide +kernel
lemma row17_0 : ∀ q : Fin (choices 0), RowValid 17 0 q := by decide +kernel
lemma row17_1 : ∀ q : Fin (choices 1), RowValid 17 1 q := by decide +kernel
lemma row17_2 : ∀ q : Fin (choices 2), RowValid 17 2 q := by decide +kernel
lemma row17_3 : ∀ q : Fin (choices 3), RowValid 17 3 q := by decide +kernel
lemma row17_4 : ∀ q : Fin (choices 4), RowValid 17 4 q := by decide +kernel
lemma row17_5 : ∀ q : Fin (choices 5), RowValid 17 5 q := by decide +kernel
lemma valid_group17 : Valid 17 := by
  refine ⟨base17.1,base17.2.1,base17.2.2,?_⟩
  intro i
  fin_cases i
  · exact row17_0
  · exact row17_1
  · exact row17_2
  · exact row17_3
  · exact row17_4
  · exact row17_5
lemma valid_sub2_1 : ∀ i : Fin 1, ValidAt (17 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group17
lemma valid_part2_1 : FiniteIntervals.Covers ValidAt 17 18 :=
  FiniteIntervals.of_fin 17 1 valid_sub2_1
lemma base18 : BaseValid 18 := by decide +kernel
lemma row18_0 : ∀ q : Fin (choices 0), RowValid 18 0 q := by decide +kernel
lemma row18_1 : ∀ q : Fin (choices 1), RowValid 18 1 q := by decide +kernel
lemma row18_2 : ∀ q : Fin (choices 2), RowValid 18 2 q := by decide +kernel
lemma row18_3 : ∀ q : Fin (choices 3), RowValid 18 3 q := by decide +kernel
lemma row18_4 : ∀ q : Fin (choices 4), RowValid 18 4 q := by decide +kernel
lemma row18_5 : ∀ q : Fin (choices 5), RowValid 18 5 q := by decide +kernel
lemma valid_group18 : Valid 18 := by
  refine ⟨base18.1,base18.2.1,base18.2.2,?_⟩
  intro i
  fin_cases i
  · exact row18_0
  · exact row18_1
  · exact row18_2
  · exact row18_3
  · exact row18_4
  · exact row18_5
lemma valid_sub2_2 : ∀ i : Fin 1, ValidAt (18 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group18
lemma valid_part2_2 : FiniteIntervals.Covers ValidAt 18 19 :=
  FiniteIntervals.of_fin 18 1 valid_sub2_2
lemma base19 : BaseValid 19 := by decide +kernel
lemma row19_0 : ∀ q : Fin (choices 0), RowValid 19 0 q := by decide +kernel
lemma row19_1 : ∀ q : Fin (choices 1), RowValid 19 1 q := by decide +kernel
lemma row19_2 : ∀ q : Fin (choices 2), RowValid 19 2 q := by decide +kernel
lemma row19_3 : ∀ q : Fin (choices 3), RowValid 19 3 q := by decide +kernel
lemma row19_4 : ∀ q : Fin (choices 4), RowValid 19 4 q := by decide +kernel
lemma row19_5 : ∀ q : Fin (choices 5), RowValid 19 5 q := by decide +kernel
lemma valid_group19 : Valid 19 := by
  refine ⟨base19.1,base19.2.1,base19.2.2,?_⟩
  intro i
  fin_cases i
  · exact row19_0
  · exact row19_1
  · exact row19_2
  · exact row19_3
  · exact row19_4
  · exact row19_5
lemma valid_sub2_3 : ∀ i : Fin 1, ValidAt (19 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group19
lemma valid_part2_3 : FiniteIntervals.Covers ValidAt 19 20 :=
  FiniteIntervals.of_fin 19 1 valid_sub2_3
lemma base20 : BaseValid 20 := by decide +kernel
lemma row20_0 : ∀ q : Fin (choices 0), RowValid 20 0 q := by decide +kernel
lemma row20_1 : ∀ q : Fin (choices 1), RowValid 20 1 q := by decide +kernel
lemma row20_2 : ∀ q : Fin (choices 2), RowValid 20 2 q := by decide +kernel
lemma row20_3 : ∀ q : Fin (choices 3), RowValid 20 3 q := by decide +kernel
lemma row20_4 : ∀ q : Fin (choices 4), RowValid 20 4 q := by decide +kernel
lemma row20_5 : ∀ q : Fin (choices 5), RowValid 20 5 q := by decide +kernel
lemma valid_group20 : Valid 20 := by
  refine ⟨base20.1,base20.2.1,base20.2.2,?_⟩
  intro i
  fin_cases i
  · exact row20_0
  · exact row20_1
  · exact row20_2
  · exact row20_3
  · exact row20_4
  · exact row20_5
lemma valid_sub2_4 : ∀ i : Fin 1, ValidAt (20 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group20
lemma valid_part2_4 : FiniteIntervals.Covers ValidAt 20 21 :=
  FiniteIntervals.of_fin 20 1 valid_sub2_4
lemma base21 : BaseValid 21 := by decide +kernel
lemma row21_0 : ∀ q : Fin (choices 0), RowValid 21 0 q := by decide +kernel
lemma row21_1 : ∀ q : Fin (choices 1), RowValid 21 1 q := by decide +kernel
lemma row21_2 : ∀ q : Fin (choices 2), RowValid 21 2 q := by decide +kernel
lemma row21_3 : ∀ q : Fin (choices 3), RowValid 21 3 q := by decide +kernel
lemma row21_4 : ∀ q : Fin (choices 4), RowValid 21 4 q := by decide +kernel
lemma row21_5 : ∀ q : Fin (choices 5), RowValid 21 5 q := by decide +kernel
lemma valid_group21 : Valid 21 := by
  refine ⟨base21.1,base21.2.1,base21.2.2,?_⟩
  intro i
  fin_cases i
  · exact row21_0
  · exact row21_1
  · exact row21_2
  · exact row21_3
  · exact row21_4
  · exact row21_5
lemma valid_sub2_5 : ∀ i : Fin 1, ValidAt (21 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group21
lemma valid_part2_5 : FiniteIntervals.Covers ValidAt 21 22 :=
  FiniteIntervals.of_fin 21 1 valid_sub2_5
lemma base22 : BaseValid 22 := by decide +kernel
lemma row22_0 : ∀ q : Fin (choices 0), RowValid 22 0 q := by decide +kernel
lemma row22_1 : ∀ q : Fin (choices 1), RowValid 22 1 q := by decide +kernel
lemma row22_2 : ∀ q : Fin (choices 2), RowValid 22 2 q := by decide +kernel
lemma row22_3 : ∀ q : Fin (choices 3), RowValid 22 3 q := by decide +kernel
lemma row22_4 : ∀ q : Fin (choices 4), RowValid 22 4 q := by decide +kernel
lemma row22_5 : ∀ q : Fin (choices 5), RowValid 22 5 q := by decide +kernel
lemma valid_group22 : Valid 22 := by
  refine ⟨base22.1,base22.2.1,base22.2.2,?_⟩
  intro i
  fin_cases i
  · exact row22_0
  · exact row22_1
  · exact row22_2
  · exact row22_3
  · exact row22_4
  · exact row22_5
lemma valid_sub2_6 : ∀ i : Fin 1, ValidAt (22 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group22
lemma valid_part2_6 : FiniteIntervals.Covers ValidAt 22 23 :=
  FiniteIntervals.of_fin 22 1 valid_sub2_6
lemma base23 : BaseValid 23 := by decide +kernel
lemma row23_0 : ∀ q : Fin (choices 0), RowValid 23 0 q := by decide +kernel
lemma row23_1 : ∀ q : Fin (choices 1), RowValid 23 1 q := by decide +kernel
lemma row23_2 : ∀ q : Fin (choices 2), RowValid 23 2 q := by decide +kernel
lemma row23_3 : ∀ q : Fin (choices 3), RowValid 23 3 q := by decide +kernel
lemma row23_4 : ∀ q : Fin (choices 4), RowValid 23 4 q := by decide +kernel
lemma row23_5 : ∀ q : Fin (choices 5), RowValid 23 5 q := by decide +kernel
lemma valid_group23 : Valid 23 := by
  refine ⟨base23.1,base23.2.1,base23.2.2,?_⟩
  intro i
  fin_cases i
  · exact row23_0
  · exact row23_1
  · exact row23_2
  · exact row23_3
  · exact row23_4
  · exact row23_5
lemma valid_sub2_7 : ∀ i : Fin 1, ValidAt (23 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group23
lemma valid_part2_7 : FiniteIntervals.Covers ValidAt 23 24 :=
  FiniteIntervals.of_fin 23 1 valid_sub2_7
lemma valid_interval2 : FiniteIntervals.Covers ValidAt 16 24 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part2_0 valid_part2_1) (FiniteIntervals.merge valid_part2_2 valid_part2_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part2_4 valid_part2_5) (FiniteIntervals.merge valid_part2_6 valid_part2_7)))
#print axioms valid_interval2
end Erdos184Work.PureSixActions2
