import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base32 : BaseValid 32 := by decide +kernel
lemma row32_0 : ∀ q : Fin (choices 0), RowValid 32 0 q := by decide +kernel
lemma row32_1 : ∀ q : Fin (choices 1), RowValid 32 1 q := by decide +kernel
lemma row32_2 : ∀ q : Fin (choices 2), RowValid 32 2 q := by decide +kernel
lemma row32_3 : ∀ q : Fin (choices 3), RowValid 32 3 q := by decide +kernel
lemma row32_4 : ∀ q : Fin (choices 4), RowValid 32 4 q := by decide +kernel
lemma row32_5 : ∀ q : Fin (choices 5), RowValid 32 5 q := by decide +kernel
lemma valid_group32 : Valid 32 := by
  refine ⟨base32.1,base32.2.1,base32.2.2,?_⟩
  intro i
  fin_cases i
  · exact row32_0
  · exact row32_1
  · exact row32_2
  · exact row32_3
  · exact row32_4
  · exact row32_5
lemma valid_sub4_0 : ∀ i : Fin 1, ValidAt (32 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group32
lemma valid_part4_0 : FiniteIntervals.Covers ValidAt 32 33 :=
  FiniteIntervals.of_fin 32 1 valid_sub4_0
lemma base33 : BaseValid 33 := by decide +kernel
lemma row33_0 : ∀ q : Fin (choices 0), RowValid 33 0 q := by decide +kernel
lemma row33_1 : ∀ q : Fin (choices 1), RowValid 33 1 q := by decide +kernel
lemma row33_2 : ∀ q : Fin (choices 2), RowValid 33 2 q := by decide +kernel
lemma row33_3 : ∀ q : Fin (choices 3), RowValid 33 3 q := by decide +kernel
lemma row33_4 : ∀ q : Fin (choices 4), RowValid 33 4 q := by decide +kernel
lemma row33_5 : ∀ q : Fin (choices 5), RowValid 33 5 q := by decide +kernel
lemma valid_group33 : Valid 33 := by
  refine ⟨base33.1,base33.2.1,base33.2.2,?_⟩
  intro i
  fin_cases i
  · exact row33_0
  · exact row33_1
  · exact row33_2
  · exact row33_3
  · exact row33_4
  · exact row33_5
lemma valid_sub4_1 : ∀ i : Fin 1, ValidAt (33 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group33
lemma valid_part4_1 : FiniteIntervals.Covers ValidAt 33 34 :=
  FiniteIntervals.of_fin 33 1 valid_sub4_1
lemma base34 : BaseValid 34 := by decide +kernel
lemma row34_0 : ∀ q : Fin (choices 0), RowValid 34 0 q := by decide +kernel
lemma row34_1 : ∀ q : Fin (choices 1), RowValid 34 1 q := by decide +kernel
lemma row34_2 : ∀ q : Fin (choices 2), RowValid 34 2 q := by decide +kernel
lemma row34_3 : ∀ q : Fin (choices 3), RowValid 34 3 q := by decide +kernel
lemma row34_4 : ∀ q : Fin (choices 4), RowValid 34 4 q := by decide +kernel
lemma row34_5 : ∀ q : Fin (choices 5), RowValid 34 5 q := by decide +kernel
lemma valid_group34 : Valid 34 := by
  refine ⟨base34.1,base34.2.1,base34.2.2,?_⟩
  intro i
  fin_cases i
  · exact row34_0
  · exact row34_1
  · exact row34_2
  · exact row34_3
  · exact row34_4
  · exact row34_5
lemma valid_sub4_2 : ∀ i : Fin 1, ValidAt (34 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group34
lemma valid_part4_2 : FiniteIntervals.Covers ValidAt 34 35 :=
  FiniteIntervals.of_fin 34 1 valid_sub4_2
lemma base35 : BaseValid 35 := by decide +kernel
lemma row35_0 : ∀ q : Fin (choices 0), RowValid 35 0 q := by decide +kernel
lemma row35_1 : ∀ q : Fin (choices 1), RowValid 35 1 q := by decide +kernel
lemma row35_2 : ∀ q : Fin (choices 2), RowValid 35 2 q := by decide +kernel
lemma row35_3 : ∀ q : Fin (choices 3), RowValid 35 3 q := by decide +kernel
lemma row35_4 : ∀ q : Fin (choices 4), RowValid 35 4 q := by decide +kernel
lemma row35_5 : ∀ q : Fin (choices 5), RowValid 35 5 q := by decide +kernel
lemma valid_group35 : Valid 35 := by
  refine ⟨base35.1,base35.2.1,base35.2.2,?_⟩
  intro i
  fin_cases i
  · exact row35_0
  · exact row35_1
  · exact row35_2
  · exact row35_3
  · exact row35_4
  · exact row35_5
lemma valid_sub4_3 : ∀ i : Fin 1, ValidAt (35 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group35
lemma valid_part4_3 : FiniteIntervals.Covers ValidAt 35 36 :=
  FiniteIntervals.of_fin 35 1 valid_sub4_3
lemma base36 : BaseValid 36 := by decide +kernel
lemma row36_0 : ∀ q : Fin (choices 0), RowValid 36 0 q := by decide +kernel
lemma row36_1 : ∀ q : Fin (choices 1), RowValid 36 1 q := by decide +kernel
lemma row36_2 : ∀ q : Fin (choices 2), RowValid 36 2 q := by decide +kernel
lemma row36_3 : ∀ q : Fin (choices 3), RowValid 36 3 q := by decide +kernel
lemma row36_4 : ∀ q : Fin (choices 4), RowValid 36 4 q := by decide +kernel
lemma row36_5 : ∀ q : Fin (choices 5), RowValid 36 5 q := by decide +kernel
lemma valid_group36 : Valid 36 := by
  refine ⟨base36.1,base36.2.1,base36.2.2,?_⟩
  intro i
  fin_cases i
  · exact row36_0
  · exact row36_1
  · exact row36_2
  · exact row36_3
  · exact row36_4
  · exact row36_5
lemma valid_sub4_4 : ∀ i : Fin 1, ValidAt (36 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group36
lemma valid_part4_4 : FiniteIntervals.Covers ValidAt 36 37 :=
  FiniteIntervals.of_fin 36 1 valid_sub4_4
lemma base37 : BaseValid 37 := by decide +kernel
lemma row37_0 : ∀ q : Fin (choices 0), RowValid 37 0 q := by decide +kernel
lemma row37_1 : ∀ q : Fin (choices 1), RowValid 37 1 q := by decide +kernel
lemma row37_2 : ∀ q : Fin (choices 2), RowValid 37 2 q := by decide +kernel
lemma row37_3 : ∀ q : Fin (choices 3), RowValid 37 3 q := by decide +kernel
lemma row37_4 : ∀ q : Fin (choices 4), RowValid 37 4 q := by decide +kernel
lemma row37_5 : ∀ q : Fin (choices 5), RowValid 37 5 q := by decide +kernel
lemma valid_group37 : Valid 37 := by
  refine ⟨base37.1,base37.2.1,base37.2.2,?_⟩
  intro i
  fin_cases i
  · exact row37_0
  · exact row37_1
  · exact row37_2
  · exact row37_3
  · exact row37_4
  · exact row37_5
lemma valid_sub4_5 : ∀ i : Fin 1, ValidAt (37 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group37
lemma valid_part4_5 : FiniteIntervals.Covers ValidAt 37 38 :=
  FiniteIntervals.of_fin 37 1 valid_sub4_5
lemma base38 : BaseValid 38 := by decide +kernel
lemma row38_0 : ∀ q : Fin (choices 0), RowValid 38 0 q := by decide +kernel
lemma row38_1 : ∀ q : Fin (choices 1), RowValid 38 1 q := by decide +kernel
lemma row38_2 : ∀ q : Fin (choices 2), RowValid 38 2 q := by decide +kernel
lemma row38_3 : ∀ q : Fin (choices 3), RowValid 38 3 q := by decide +kernel
lemma row38_4 : ∀ q : Fin (choices 4), RowValid 38 4 q := by decide +kernel
lemma row38_5 : ∀ q : Fin (choices 5), RowValid 38 5 q := by decide +kernel
lemma valid_group38 : Valid 38 := by
  refine ⟨base38.1,base38.2.1,base38.2.2,?_⟩
  intro i
  fin_cases i
  · exact row38_0
  · exact row38_1
  · exact row38_2
  · exact row38_3
  · exact row38_4
  · exact row38_5
lemma valid_sub4_6 : ∀ i : Fin 1, ValidAt (38 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group38
lemma valid_part4_6 : FiniteIntervals.Covers ValidAt 38 39 :=
  FiniteIntervals.of_fin 38 1 valid_sub4_6
lemma base39 : BaseValid 39 := by decide +kernel
lemma row39_0 : ∀ q : Fin (choices 0), RowValid 39 0 q := by decide +kernel
lemma row39_1 : ∀ q : Fin (choices 1), RowValid 39 1 q := by decide +kernel
lemma row39_2 : ∀ q : Fin (choices 2), RowValid 39 2 q := by decide +kernel
lemma row39_3 : ∀ q : Fin (choices 3), RowValid 39 3 q := by decide +kernel
lemma row39_4 : ∀ q : Fin (choices 4), RowValid 39 4 q := by decide +kernel
lemma row39_5 : ∀ q : Fin (choices 5), RowValid 39 5 q := by decide +kernel
lemma valid_group39 : Valid 39 := by
  refine ⟨base39.1,base39.2.1,base39.2.2,?_⟩
  intro i
  fin_cases i
  · exact row39_0
  · exact row39_1
  · exact row39_2
  · exact row39_3
  · exact row39_4
  · exact row39_5
lemma valid_sub4_7 : ∀ i : Fin 1, ValidAt (39 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group39
lemma valid_part4_7 : FiniteIntervals.Covers ValidAt 39 40 :=
  FiniteIntervals.of_fin 39 1 valid_sub4_7
lemma valid_interval4 : FiniteIntervals.Covers ValidAt 32 40 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part4_0 valid_part4_1) (FiniteIntervals.merge valid_part4_2 valid_part4_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part4_4 valid_part4_5) (FiniteIntervals.merge valid_part4_6 valid_part4_7)))
#print axioms valid_interval4
end Erdos184Work.PureSixActions2
